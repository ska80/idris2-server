module Server

-- import Control.Monad.Syntax
import Control.Monad.Identity
import Control.Monad.Converter

import Data.IORef
import public Data.String.ParserInterface
import Data.Either
import Data.Vect
import public Data.List
import Data.List1
import Data.Strings
import Decidable.Equality

import Server.Utils

import public Records

%default total

public export
data Verb : Type where
  Get : Verb
  Post : (body : Type) -> HasParser body => Verb

namespace IndexedRecords
  ||| Value for a row given a key
  public export
  data RowVal : String -> Type -> Type where
    (:=:) : (s : String) -> (val : t) -> HasParser t => RowVal s t

  public export
  data IRecord : Record -> Type where
    Nil : IRecord []
    (::) :  HasParser t => RowVal s t ->
            IRecord rs -> IRecord (s :=: t :: rs)

||| A Type for Paths that can have a common prefix.
public export
data Path : Type where
  Ends : (queryItems: Maybe Record)
      -> (returnType : Type)
      -> Show returnType
      => (v : Verb)
      -> Path
  Plain : String -> (ps : Path) -> Path
  Capture : (name : String) -> (t : Type) -> HasParser t => (ps : Path) -> Path
  Split : List Path -> Path

||| Is the endpoint querying the state or updating the state?
||| `Type` here is the type of the state
public export
data RequestBody : Type where
  Query : (st : Type) -> Show st => RequestBody
  Update : (val : Type) -> HasParser val => (st : Type) -> Show st => RequestBody

public export
StTy : RequestBody -> Type
StTy (Query st) = st
StTy (Update _ st) = st

||| The types associated with state updates that are in argument position
public export
ArgTy : RequestBody -> Type
ArgTy (Query st) = st
ArgTy (Update val st) = (val, st)

||| The type we need to parse from the request body
public export
ParseArgReq : RequestBody -> Type
ParseArgReq (Query _) = ()
ParseArgReq (Update val _) = val

public export
Args4Req : RequestBody -> Nat
Args4Req (Query st) = Z
Args4Req (Update val st) = 1

||| A Type for full path components.
-- public export
-- data PathComp : Nat -> Type -> Type where
--   End : (q : Maybe Record) -> (update : RequestBody) -> (ret : Type) -> Show ret => PathComp Z (RTy update)
--   Str : String -> PathComp n rqt -> PathComp (S n) rqt
--   Tpe : (t : Type) -> HasParser t => PathComp n rqt -> PathComp (S n) rqt
public export
data PathComp : Nat -> (state : Type) -> Type where
  End : (q : Maybe Record) -> (update : RequestBody) -> (ret : Type) -> Show ret => PathComp (Args4Req update) (StTy update)
  Str : String -> PathComp n st -> PathComp (S n) st
  Tpe : (t : Type) -> HasParser t => PathComp n st -> PathComp (S n) st

export
Show (PathComp n st) where
  show (End Nothing (Query _) ret) = "returns: '" ++ ShowType ret ++ "'"
  show (End Nothing (Update body _) ret) = "returns: '" ++ ShowType ret ++ "' body : \{ShowType body}'"
  show (End (Just q) update ret) = show q ++ "/" ++ assert_total (show (End Nothing update ret))
  show (Str x y) = x ++ "/" ++ show y
  show (Tpe t x) = ":\{ShowType t}/" ++ show x

||| Convert a PathComp into a function type
public export
PathCompToType : PathComp n st -> Type
PathCompToType (End Nothing (Update val st) ret) = val -> st -> (ret, st)
PathCompToType (End Nothing (Query st) ret) = st -> ret
PathCompToType (End (Just rec) (Update val st) ret) = IRecord rec -> val -> st -> (ret, st)
PathCompToType (End (Just rec) (Query st) ret) = IRecord rec -> st -> ret
PathCompToType (Str x y) = PathCompToType y
PathCompToType (Tpe x y) = x -> PathCompToType y

||| Convert a PathComp into a tuple of arguments for the corresponding function type
public export
Args : PathComp n st -> Type
Args (End Nothing (Query st) t) = st
Args (End Nothing (Update val st) t) = (val, st)
Args (End (Just rec) (Query st) t) = (IRecord rec, st)
Args (End (Just rec) (Update val st) t) = (IRecord rec, val, st)
Args (Str s ps) = Args ps
Args (Tpe t ps) = (t, Args ps)

||| Convert a path comp into the tuple of arguments to parse in an incoming request
public export
ParseArgs : PathComp n st -> Type
ParseArgs (End Nothing (Update val _ ) t) = val
ParseArgs (End Nothing (Query _) t) = ()
ParseArgs (End (Just rec) (Update val _) t) = (IRecord rec, val)
ParseArgs (End (Just rec) (Query _) t) = IRecord rec
ParseArgs (Str s ps) = ParseArgs ps
ParseArgs (Tpe t ps) = (t, ParseArgs ps)

||| Arguments needed for state management
||| Args path = ParseArgs path ++ StateArgs path
public export
StateArgs : PathComp n st -> Type
StateArgs (End q update ret) = ArgTy update
StateArgs (Str x y) = StateArgs y
StateArgs (Tpe t x) = StateArgs x

ToStateArgs : (PathComp n st) -> ParseArgs path -> st -> StateArgs path

||| Return type of the corresponding function type from a PathComp
public export
Ret : PathComp n st -> Type
Ret (End q (Update _ st) ret) = (ret, st)
Ret (End q (Query st) ret) = ret
Ret (Str _ ps) = Ret ps
Ret (Tpe _ ps) = Ret ps

public export
fromHandle : (path : PathComp n st) -> st -> (Args path -> Ret path) -> ParseArgs path -> Ret path
fromHandle (End Nothing (Query st) ret) state f x = f state
fromHandle (End (Just y) (Query st) ret) state f x = f (x, state)
fromHandle (End Nothing (Update val st) ret) state f x = f (x, state)
fromHandle (End (Just y) (Update val st) ret) state f x = f (fst x, (snd x, state))
fromHandle (Str y z) state f x = fromHandle z state f x
fromHandle (Tpe t y) state f x = fromHandle y state (\z => f (fst x, z)) (snd x)

||| Converts a PathComp into an uncurried function from a tuple of arguments into its return type
public export 0
PathToArgs : PathComp n st -> Type
PathToArgs path = Args path -> Ret path

||| Converts a function type into its uncurried variant
export
convertPathFuncs : {path : PathComp n st} -> PathCompToType path -> Args path -> Ret path
convertPathFuncs f x {path = (End Nothing (Update val st) ret)} = f (fst x) (snd x)
convertPathFuncs f x {path = (End Nothing (Query st) ret)} = f x
convertPathFuncs f (rec', (val', state)) {path = (End (Just rec) (Update val st) ret)} = f rec' val' state
convertPathFuncs f arg {path = (End (Just rec) (Query st) ret)} = f (fst arg) (snd arg)
convertPathFuncs x y {path = (Str s p)} = convertPathFuncs x y {path=p}
convertPathFuncs f (v, args) {path = (Tpe t p)} = convertPathFuncs (f v) args {path=p}

||| A List of functions indexed by a list of PathComp which define each function's signature
public export
data PathList : (0 _ : List (n ** PathComp n st)) -> Type where
  Nil : PathList []
  (::) : (p : PathCompToType (DPair.snd t)) -> PathList ts -> PathList (t :: ts)

public export
TypeList : Type
TypeList = List (Either String (s : Type ** HasParser s))

public export
mkComponents : Maybe Record -> (req : RequestBody) -> TypeList -> (t : Type) -> Show t => (n ** PathComp n (StTy req))
mkComponents rec req [] x = (Args4Req req ** End rec req x)
mkComponents rec req (Left str :: xs) x =
  let (n ** ts) = mkComponents rec req xs x in
      (S n ** Str str ts)
mkComponents rec req (Right (r ** s) :: xs) x =
  let (n ** ys) = mkComponents rec req xs x in
      (S n ** Tpe r ys)

parameters (state : Type) {auto showI : Show state}
  ||| Maps a Path to a list of PathComponents.
  ||| The prefix is repeated for each branching path
  ||| in the resulting list
  |||
  ||| The following path:
  ||| a━━b━━c
  |||    ┣━━d
  |||    ┗━━e━━f
  |||       ┗━━g
  ||| Will be mapped into
  |||
  ||| [ a━━b━━c
  ||| , a━━b━━d
  ||| , a━━b━━e━━f
  ||| , a━━b━━e━━g
  ||| ]
  public export
  toComponents : (pre : TypeList) -> (path : Path) -> List (n ** PathComp n state)
  toComponents pre (Ends rec t Get) =
    pure $ mkComponents rec (Query state) (reverse pre) t
  toComponents pre (Ends rec t (Post val)) =
    pure $ mkComponents rec (Update val state) (reverse pre) t
  toComponents pre (Plain name ps) = toComponents (Left name :: pre) ps
  toComponents pre (Capture name t ps) = toComponents (Right (t ** %search) :: pre) ps
  toComponents pre (Split xs) =  xs >>= assert_total (toComponents pre)

||| Maps a Path into a list of functions
|||
||| The common prefix for paths splittingis duplicated between each function
||| so that the user of the API doesn't have to concern themselves with
||| the structure of the API and implement and avoid implementing partially
||| applied functions.
public export
Signature : (state : Type) -> Show state => Path -> Type
Signature state path = PathList $ (toComponents state [] path)

FromSignature : {path : Path} -> Signature () path
             -> List (n ** p : PathComp n () ** (Args p -> Ret p))
FromSignature ps {path} = signatureHelp ps
  where
    signatureHelp : {fnPath : List (n ** PathComp n ())} -> PathList fnPath
                 -> List (n ** p : PathComp n () ** (Args p -> Ret p))
    signatureHelp [] {fnPath = []} = []
    signatureHelp (p :: ps) {fnPath = ((n ** path) :: ts)} =
      (n ** (path ** convertPathFuncs p)) :: signatureHelp ps

public export
data ServerError : Type where
  WrongArgumentLength : Show a => (n : Nat) -> List a -> PathComp n st -> ServerError
  UnexpectedPath : (expected, actual : String) -> ServerError
  ParseError : (message : String) -> ServerError
  UnhandledPath : List String -> ServerError
  Aggregate : List ServerError -> ServerError
  QueryLength : ServerError
  UnexpectedQueryItem : (expected, actual : String) -> ServerError

export
Show ServerError where
  show (WrongArgumentLength k xs p) =
    "Expected " ++ show k ++ " arguments, got " ++ show (length xs) ++ "." ++
      " Expected path: " ++ show p ++
      " Actual path: " ++ show xs
  show (UnexpectedPath expected actual) =
    "Expected path component " ++ show expected ++ ", got " ++ show actual ++ " instead."
  show (ParseError message) =
    "Parse error: " ++ show message ++ "."
  show (UnhandledPath xs) =
    "Path not handled by server: " ++ show xs ++ "."
  show (Aggregate xs) =
    "Multiple errors: \n" ++ unlines (map (\x => " - " ++ (assert_total show) x) xs)
  show QueryLength =
    "Query items have the wrong length"
  show (UnexpectedQueryItem expected actual) =
    "Expected key '" ++ expected ++ "' got '" ++ actual ++ "' instead."

public export
ServerM : Type -> Type
ServerM = Either ServerError

parseToServerError : Parser a -> String -> ServerM a
parseToServerError p s = maybeToEither (ParseError $ "could not parse " ++ s) (p s)

public export
fieldParser : (rec : Record) -> List (String, String) -> ServerM (IRecord rec)
fieldParser [] [] = pure []
fieldParser ((f :=: t) :: rs) ((key, value) :: xs) with (decEq key f)
  fieldParser ((f :=: t) :: rs) ((key, value) :: xs) | Yes with_pat = do
       v <- parseToServerError (parse {t}) value
       rest <- fieldParser rs xs
       pure (f :=: v :: rest)
  fieldParser ((f :=: t) :: rs) ((key, value) :: xs) | No with_pat =
    Left $ UnexpectedQueryItem f key
fieldParser _ _ = Left QueryLength

||| Given a path, generate a function that parses the arguments from a URL
||| @path : The path to parse
||| @queryItems : The query items from the URL
||| @components : The component paths from the URL
public export
makeParser : (path : PathComp n st) ->
             (List (String, String)) ->
             Vect n String ->
             ServerM (ParseArgs path)
makeParser (End Nothing (Query st) _) query [] = Right ()
makeParser (End Nothing (Update val  st) _) query [v] = parseToServerError (parse {t=val}) v
makeParser (End (Just rec) (Query st) t) query [] = fieldParser rec query
makeParser (End (Just rec) (Update val st) t) query [v] = do v' <- parseToServerError (parse {t=val}) v
                                                             qu <- fieldParser rec query
                                                             pure (qu, v')
makeParser (Str s ps) query (z :: xs) =
  if s == z
     then makeParser ps query xs
     else Left $ UnexpectedPath s z
makeParser (Tpe t ps) query (z :: xs) =
  [| MkPair (parseToServerError (parse {t}) z)
            (makeParser ps query xs) |]

{-
-}

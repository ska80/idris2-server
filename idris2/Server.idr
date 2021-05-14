module Server

-- import Control.Monad.Syntax
import Control.Monad.Identity
import Control.Monad.Converter
import public Data.String.ParserInterface
import Data.Either
import Data.Vect
import public Data.List
import Data.List1
import Data.Strings
import Decidable.Equality

import public Records

%default total

export
orElse : Either a b -> Either a b -> Either a b
orElse (Left x) y = y
orElse (Right x) y = Right x

public export
data Verb = Get | Patch | Post | Put

public export
data StatusCode : Nat -> Type where
  -- 2xx
  Ok : StatusCode 200
  Created : StatusCode 201
  Accepted : StatusCode 202
  -- 3xx
  Mutliple : StatusCode 300
  Moved : StatusCode 301

  -- 4xx
  Bad : StatusCode 400
  Unauthorized : StatusCode 401
  -- Payment : StatusCode 402
  Forbidden : StatusCode 403
  NotFound : StatusCode 404

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
      -> (s : StatusCode n)
      -> Path
  Plain : String -> (ps : Path) -> Path
  Capture : (name : String) -> (t : Type) -> HasParser t => (ps : Path) -> Path
  Split : List Path -> Path

||| A Type for full path components.
public export
data PathComp : (m : Type -> Type) -> Nat -> Type where
  End : (q : Maybe Record) -> (ret : Type) -> Show ret => PathComp m Z
  Str : String -> PathComp m n -> PathComp m (S n)
  Tpe : (t : Type) -> HasParser t => PathComp m n -> PathComp m (S n)

Show (PathComp m n) where
  show (End q ret) = "return"
  show (Str x y) = x ++ "/" ++ show y
  show (Tpe t x) = "type/" ++ show x

||| Convert a PathComp into a function type
public export
PathCompToType : {m : _} -> PathComp m n -> Type
PathCompToType (End Nothing ret) = m ret
PathCompToType (End (Just rec) ret) = IRecord rec -> m ret
PathCompToType (Str x y) = PathCompToType y
PathCompToType (Tpe x y) = x -> PathCompToType y

||| Convert a PathComp into a tuple of arguments for the corresponding function type
public export
Args : PathComp m n -> Type
Args (End Nothing t) = ()
Args (End (Just rec) t) = IRecord rec
Args (Str s ps) = Args ps
Args (Tpe t ps) = (t, Args ps)

||| Ends the return type of the corresponding function type from a PathComp
public export
Ret : {m : _} -> PathComp m n -> Type
Ret (End q t) {m} = m t
Ret (Str _ ps) = Ret ps
Ret (Tpe _ ps) = Ret ps

||| Converts a PathComp into an uncurried function from a tuple of argument into its return type
0
PathToArgs : PathComp m n -> Type
PathToArgs path = Args path -> Ret path

||| Converts a function type into its uncurried variant
export
convertPathFuncs : {path : PathComp m n} -> PathCompToType path -> Args path -> Ret path
convertPathFuncs x y {path = (End Nothing ret)} = x
convertPathFuncs f arg {path = (End (Just rec) ret)} = f arg
convertPathFuncs x y {path = (Str s p)} = convertPathFuncs x y {path=p}
convertPathFuncs f (v, args) {path = (Tpe t p)} = convertPathFuncs (f v) args {path=p}

||| A List of functions indexed by a list of PathComp which define each function's signature
public export
data PathList : (0 _ : List (n ** PathComp m n)) -> Type where
  Nil : PathList []
  (::) : (p : PathCompToType (DPair.snd t)) -> PathList ts -> PathList (t :: ts)

infixr 5 //

public export
data Capt : Type where
  Cap : (name : String) -> (t : Type) -> HasParser t => Capt

public export
interface PathBuilder t where
  (//) : t -> Path -> Path

public export
PathBuilder String where
  (//) = Plain

public export
PathBuilder Capt where
  (//) (Cap n t) p = Capture n t p


public export
Query :  Record -> (t : Type) -> Show t =>
       (v : Verb) -> (s : StatusCode n) -> Path
Query rec t v s = Ends (Just rec) t v s

public export
Returns : (t : Type) -> Show t =>
        (v : Verb) -> (s : StatusCode n) -> Path
Returns t v s = Ends Nothing t v s


public export
TypeList : Type
TypeList = List (Either String (s : Type ** HasParser s))

public export
mkComponents : Maybe Record -> TypeList -> (t : Type) -> Show t => (n ** PathComp m n)
mkComponents rec [] x = (Z ** End rec x)
mkComponents rec (Left str :: xs) x =
  let (n ** ts) = mkComponents rec xs x in
      (S n ** Str str ts)
mkComponents rec (Right (r ** s) :: xs) x =
  let (n ** ys) = mkComponents rec xs x in
      (S n ** Tpe r ys)

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
toComponents : (pre : TypeList) -> (path : Path) -> List (n ** PathComp m n)
toComponents pre (Ends rec t v s) =
  pure $ mkComponents rec (reverse pre) t
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
Signature : (0 m : Type -> Type) -> Path -> Type
Signature m path = PathList (toComponents [] path {m})

FromSignature : {path : Path} -> Signature m path
             -> List (n ** p : PathComp m n ** (Args p -> Ret p))
FromSignature ps {path} = signatureHelp ps
  where
    signatureHelp : {fnPath : List (n ** PathComp m n)} -> PathList fnPath
                 -> List (n ** p : PathComp m n ** (Args p -> Ret p))
    signatureHelp [] {fnPath = []} = []
    signatureHelp (p :: ps) {fnPath = ((n ** path) :: ts)} =
      (n ** (path ** convertPathFuncs p)) :: signatureHelp ps

public export
data ServerError : Type where
  WrongArgumentLength : Show a => (n : Nat) -> List a -> PathComp m n -> ServerError
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
export
makeParser : (path : PathComp m n)
          -> (queryItems : List (String, String))
          -> (components: Vect n String)
          -> ServerM (Args path)
makeParser (End Nothing t) query [] = pure ()
makeParser (End (Just rec) t) query [] = fieldParser rec query
makeParser (Str s ps) query (z :: xs) =
  if s == z
     then makeParser ps query xs
     else Left $ UnexpectedPath s z
makeParser (Tpe t ps) query (z :: xs) =
  [| MkPair (parseToServerError (parse {t}) z)
            (makeParser ps query xs) |]

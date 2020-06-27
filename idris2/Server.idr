module Server

import public Data.Vect
import Data.List
import Data.Strings

%default total

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

export
Parser : Type -> Type
Parser t = String -> Maybe t

public export
interface HasParser t where
  parse : Parser t

export
HasParser Int where
  parse = ?parseInteger

export
HasParser String where
  parse = Just

||| A Type for Paths that can have a common prefix.
public export
data Path : Type where
  Returns : (t : Type) -> Show t => (v : Verb) -> (s : StatusCode n) -> Path
  Plain : String -> (ps : Path) -> Path
  Capture : (name : String) -> (t : Type) -> HasParser t => (ps : Path) -> Path
  Split : List Path -> Path

||| A Type for full path components.
public export
data PathComp : Nat -> Type where
  End : (ret : Type) -> Show ret => PathComp Z
  Str : String -> PathComp n -> PathComp (S n)
  Tpe : (t : Type) -> HasParser t => PathComp n -> PathComp (S n)

||| Convert a PathComp into a function type
public export
PathCompToType : PathComp n -> Type
PathCompToType (End ret) = ret
PathCompToType (Str x y) = PathCompToType y
PathCompToType (Tpe x y) = x -> PathCompToType y

||| Convert a PathComp into a tuple of arguments for the corresponding function type
Args : PathComp n -> Type
Args (End t) = ()
Args (Str s ps) = Args ps
Args (Tpe t ps) = (t, Args ps)

||| Returns the return type of the corresponding function type from a PathComp
Ret : PathComp n -> Type
Ret (End t) = t
Ret (Str _ ps) = Ret ps
Ret (Tpe _ ps) = Ret ps

||| Converts a PathComp into an uncurried function from a tuple of argument into its return type
PathToArgs : PathComp n -> Type
PathToArgs path = Args path -> Ret path

||| Converts a function type into its uncurried variant
convertPathFuncs : {path : PathComp n} -> PathCompToType path -> Args path -> Ret path
convertPathFuncs x y {path = (End ret)} = x
convertPathFuncs x y {path = (Str s p)} = convertPathFuncs x y {path=p}
convertPathFuncs f (v, args) {path = (Tpe t p)} = convertPathFuncs (f v) args {path=p}

||| A List of functions indexed by a list of PathComp which define each function's signature
public export
data PathList : List (n ** PathComp n) -> Type where
  Nil : PathList []
  (::) : (p : PathCompToType (DPair.snd t)) -> PathList ts -> PathList (t :: ts)

infixr 5 //

public export
data Capt : Type where
  Cap : (name : String) -> (t : Type) -> HasParser t => Capt

export
interface PathBuilder t where
  (//) : t -> Path -> Path

public export
PathBuilder String where
  (//) = Plain

public export
PathBuilder Capt where
  (//) (Cap n t) p = Capture n t p

public export
TypeList : Type
TypeList = List (Either String (s : Type ** HasParser s))

public export
mkComponents : TypeList -> (t : Type) -> Show t => (n ** PathComp n)
mkComponents []                       x = (Z ** End x)
mkComponents ((Left l) :: xs)         x = let (n ** ys) = mkComponents xs x in (S n ** Str l ys)
mkComponents ((Right (r ** s)) :: xs) x = let (n ** ys) = mkComponents xs x in (S n ** Tpe r ys)

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
toComponents : (pre : TypeList) -> (path : Path) -> List (n ** PathComp n)
toComponents pre (Returns t v s) = pure $ mkComponents (reverse pre) t
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
Signature : Path -> Type
Signature path = PathList (toComponents [] path)

FromSignature : {path : Path} -> Signature path -> List (n ** p : PathComp n ** (Args p -> Ret p))
FromSignature ps {path} = signatureHelp ps
  where
    signatureHelp : {fnPath : List (m ** PathComp m)} -> PathList fnPath
                 -> List (n ** p : PathComp n ** (Args p -> Ret p))
    signatureHelp [] {fnPath = []} = []
    signatureHelp (p :: ps) {fnPath = ((n ** path) :: ts)} =
      (n ** path ** convertPathFuncs p) :: signatureHelp ps

makeParser : (path : PathComp n)
        -> Vect n String -> Maybe (Args path)
makeParser (End t) [] = Just ()
makeParser (Str s ps) (z :: xs) = if s == z then makeParser ps xs else Nothing
makeParser (Tpe t ps) (z :: xs) =
  [| MkPair (parse {t} z) (makeParser ps xs) |]

Handler : PathComp n -> Type
Handler path = Args path -> Ret path

-- Here the handlers are both parsing the string and returning the result of
-- the comutation as an encoded string. This is to void leaking the detail of
-- the dependency between the parsed type and the type of the handler.
partial
server : (handlers : List (List String -> Maybe String)) -> IO ()
server handlers = do
    str <- getLine
    let Just result = tryAll handlers (split (== '/') str)
      | _ => putStrLn ("could not parse " ++ str)
    putStrLn result
    server handlers
  where
    tryAll : List (List String -> Maybe String) -> List String -> Maybe String
    tryAll [] input = Nothing
    tryAll (f :: fs) input = f input <|> tryAll fs input

||| Returns a printing function for the return type of a given PathComp
pathCompToPrintRet : (p : PathComp n) -> (Ret p) -> String
pathCompToPrintRet (End ret) x = show x
pathCompToPrintRet (Str _ ps) x = pathCompToPrintRet ps x
pathCompToPrintRet (Tpe _ ps) x = pathCompToPrintRet ps x

||| Make a function to handle server request from a path
|||
||| This combines 3 functions, one to parse the URL path and
||| extract the arguments from it. One to perform an operation on the
||| parsed arguments, and one to print the final result.
||| The resulting functions hides all details about the intermediate
||| types used to parse the incoming request and operates on Strings
||| only.
||| @ length : The length of the path
||| @ path : The URL path
||| @ showResult : The printer function for the computed result
||| @ handler : The operation to perform on the parsed arguments
stringSig : (length : Nat) -> (path : PathComp length)
         -> (parsePath : Vect length String -> Maybe (Args p))
         -> (showResult : Ret p -> String)
         -> (handler : Args p -> Ret p)
         -> (List String -> Maybe String)
stringSig n p parser printer handler =
    map (printer . handler) . (\x => checkLength n x >>= parser)
  where
    checkLength : (n : Nat) -> List a -> Maybe (Vect n a)
    checkLength n ls = exactLength n $ fromList ls

||| Given an implementation of a path, return a list of function for each possible route
handleAllPaths : {path : List (m ** PathComp m)} -> PathList path -> List (List String -> Maybe String)
handleAllPaths [] {path = []} = []
handleAllPaths (v :: vs) {path = ((n ** comp) :: ts)} =
    stringSig n comp (makeParser comp) (pathCompToPrintRet comp) (convertPathFuncs v)
      :: handleAllPaths vs {path=ts}

||| Given an implementation of a path, return a list of function for each possible route
forAllPaths : {path : Path} -> Signature path -> List (List String -> Maybe String)
forAllPaths x {path} = handleAllPaths x

||| Instanciate a new sever given a path and an implementation for it.
|||
||| @ path : The server's API as a Path
||| @ impl : The servver's implementation of the exposed API
export partial
newServer : (path : Path)
         -> (impl : Signature path)
         -> IO ()
newServer path impl = server (forAllPaths impl)


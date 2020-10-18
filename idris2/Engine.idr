module Engine

import Data.List1
import Data.Strings
import Data.Maybe
import Data.Either
import Data.Vect
import Server
import URL

Handler : Type
Handler = (components : List String) 
       -> (queryItems : List (String, String))
       -> ServerM String

-- Here the handlers are both parsing the string and returning the result of
-- the comutation as an encoded string. This is to void leaking the detail of
-- the dependency between the parsed type and the type of the handler.
partial
server : (handlers : List Handler) -> IO ()
server handlers = do
    str <- getLine
    let (Just (url ** (MkURL scheme
                             (Just auth)
                             valid
                             query
                             fragment))) = parseURL str
      | _ => putStrLn ("Could not parse url " ++ str)
          *> server handlers
    let (Absolute p) = parsePath (path url)
        | (Relative x) => putStrLn ("Expected absolute path, but got relative path"
                       ++ show x)
                       *> server handlers

    let result = tryAll [] handlers (forget p) query
    either printLn putStrLn result
    server handlers
  where
    bindFst : (a -> Either a b) -> Either a b -> Either a b
    bindFst f (Left x) = f x
    bindFst f (Right x) = Right x

    tryAll : List ServerError -> List Handler -> Handler
    tryAll errors [] input query = Left $ Aggregate errors
    tryAll errors (f :: fs) input query =
      bindFst (\err => tryAll (err :: errors) fs input query) (f input query)

||| Returns a printing function for the return type of a given PathComp
pathCompToPrintRet : (p : PathComp n) -> (Ret p) -> String
pathCompToPrintRet (End _ ret) x = show x
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
||| @ parsePath : The parsing function that returns parsed arguments
||| @ showResult : The printer function for the computed result
||| @ handler : The operation to perform on the parsed arguments
stringSig : (length : Nat)
         -> (path : PathComp length)
         -> (parsePath : (queryItems : List (String, String))
                      -> (components : Vect length String)
                      -> ServerM (Args p))
         -> (showResult : Ret p -> String)
         -> (handler : Args p -> Ret p)
         -> Handler
stringSig n p parser printer handler path query =
  map (printer . handler) (checkLength path >>= parser query)
  where
    checkLength : Show a => List a -> ServerM (Vect n a)
    checkLength ls = maybeToEither (WrongArgumentLength n ls p )
                                   (exactLength n $ fromList ls)

||| Given an implementation of a path, return a list of function for each possible route
handleAllPaths : (path : List (m ** PathComp m)) -> PathList path -> List Handler
handleAllPaths [] [] = []
handleAllPaths ((n ** comp) :: ts) (v :: vs)  =
    stringSig n comp (makeParser comp) (pathCompToPrintRet comp) (convertPathFuncs v)
      :: handleAllPaths ts vs

||| Given an implementation of a path, return a list of function for each possible route
forAllPaths : (path : Server.Path) -> Signature path
           -> List Handler
forAllPaths path x = handleAllPaths (toComponents [] path)  x

||| Instanciate a new sever given a path and an implementation for it.
|||
||| @ path : The server's API as a Path.
||| @ impl : The server's implementation of the exposed API.
export partial
newServer : (path : Server.Path)
         -> (impl : Signature path)
         -> IO ()
newServer path impl = server (forAllPaths path impl)


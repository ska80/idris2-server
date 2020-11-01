module Engine

import Control.Monad.Converter
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
       -> IO (ServerM String)

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
    let (Absolute (p ::: ps)) = parsePath (path url)
        | (Relative x) => putStrLn ("Expected absolute path, but got relative path"
                       ++ show x)
                       *> server handlers
    let urlPath = if p == "" then [] else p :: ps
    result <- tryAll [] handlers urlPath query
    either printLn putStrLn result
    server handlers
  where
    -- Returns a handler that combines all handlers from a list by
    -- successively trying to apply them in order
    tryAll : List ServerError -> List Handler -> Handler
    tryAll errors [] input query = pure $ Left $ Aggregate errors
    tryAll errors (f :: fs) input query =
      do Right v <- f input query
           | Left err => tryAll (err :: errors) fs input query
         pure (Right v)

||| Returns a printing function for the return type of a given PathComp
pathCompToPrintRet : Applicative m => (p : PathComp m n) -> (Ret p) -> m String
pathCompToPrintRet (End _ ret) x = map show x
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
stringSig : Applicative m
         => (m =*> IO)
         => (length : Nat)
         -> (path : PathComp m length)
         -> (parsePath : (queryItems : List (String, String))
                      -> (components : Vect length String)
                      -> ServerM (Args p))
         -> (showResult : Ret p -> m String)
         -> (handler : Args p -> Ret p)
         -> Handler
stringSig n p parser printer handler path query =
  let handle = (printer . handler)
      parsed = (checkLength path >>= parser query) in
      lift (traverse handle parsed)
  where
    checkLength : Show a => List a -> ServerM (Vect n a)
    checkLength ls = maybeToEither (WrongArgumentLength n ls p )
                                   (exactLength n $ fromList ls)

||| Given an implementation of a path, return a list of function for each possible route
handleAllPaths : Applicative m => (m =*> IO)
              => (path : List (n ** PathComp m n)) -> PathList path -> List Handler
handleAllPaths [] [] = []
handleAllPaths ((n ** comp) :: ts) (v :: vs)  =
       let paths =  handleAllPaths ts vs
           path = stringSig n comp (makeParser comp)
                                   (pathCompToPrintRet comp)
                                   (convertPathFuncs v) in
           path :: paths

||| Given an implementation of a path, return a list of function for each possible route
forAllPaths : Applicative m => m =*> IO => (path : Server.Path) -> Signature m path
           -> List Handler
forAllPaths path x = handleAllPaths (toComponents [] path)  x

||| Instanciate a new sever given a path and an implementation for it.
|||
||| @ path : The server's API as a Path.
||| @ impl : The server's implementation of the exposed API.
export partial
newServer : Applicative m => m =*> IO
         => (path : Server.Path)
         -> (impl : Signature m path)
         -> IO ()
newServer path impl = server (forAllPaths path impl)


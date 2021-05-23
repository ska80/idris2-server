module Engine

import Control.Monad.Converter
import Data.IORef
import Data.List1
import Data.Strings
import Data.Maybe
import Data.Either
import Data.Vect
import Server
import Server.Utils
import URL
import Requests

-- A Handler attemps to parse the request and uses the current state to compute a response
Handler : Type -> Type
Handler state
        = state
       -> (components : List String)
       -> (queryItems : List (String, String))
       -> IO (ServerM String)

-- Here the handlers are both parsing the string and returning the result of
-- the comutation as an encoded string. This is to void leaking the detail of
-- the dependency between the parsed type and the type of the handler.
partial
server : {state : Type} -> IORef state -> (handlers : List (Handler state)) -> IO ()
server st handlers = do
    str <- getLine
    currentState <- readIORef st
    let Just (path, body) = parseRequest str
      | _ => putStrLn ("Could not parse url " ++ str)
          *> server st handlers
    -- let (Absolute (p ::: ps)) = parsePath (path url)
    --     | (Relative x) => putStrLn ("Expected absolute path, but got relative path"
    --                    ++ show x)
    --                    *> server st handlers
    -- let urlPath = if p == "" then [] else p :: ps
    let path' = maybe path (snoc path) body
    result <- tryAll [] handlers currentState path' []
    either printLn putStrLn result
    server st handlers
  where
    -- Returns a handler that combines all handlers from a list by
    -- successively trying to apply them in order
    tryAll : List ServerError -> List (Handler state) -> Handler state
    tryAll errors [] state input query = pure $ Left $ Aggregate errors
    tryAll errors (f :: fs) state input query =
      either (\err => tryAll (err :: errors) fs state input query) (pure . Right) !(f state input query)

||| Returns a printing function for the return type of a given PathComp
pathCompToPrintRet : (p : PathComp n st) -> Ret p -> String
pathCompToPrintRet (End _ (Update val st) ret) x = show x
pathCompToPrintRet (End _ (Query st) ret) x = show x
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
stringSig : {state : Type} ->
            IORef state ->
            (length : Nat) ->
            (p : PathComp length state) ->
            (parsePath : (queryItems : List (String, String)) ->
                         (components : Vect length String) ->
                         ServerM (ParseArgs p)) ->
            (showResult : Ret p -> String) ->
            (handler : Args p -> Ret p) ->
            Handler state
stringSig ref n p parser printer handler state path query =
  let
      parsed = checkLength path >>= parser query -- have the arguments been parsed?
      handle = fromHandle p state handler -- given the arguments, print the result
      val = map handle parsed
   in traverse (\v => updateRet p ref v *> pure ("Response: Ok " ++ printer v)) val
  where
    updateRet : {n : Nat} -> (path : PathComp n st) -> IORef st -> Ret path -> IO ()
    updateRet (End rec (Query st) ret) {n=Z} ref y = pure ()
    updateRet (End rec (Update val st) ret) {n=1} ref (_, newState) = writeIORef ref newState
    updateRet (Str _ p) {n=S n} ref y = updateRet p ref y
    updateRet (Tpe _ p) {n=S n} ref y = updateRet p ref y
    updateRet _ _ _ = ?impossible -- bug with coverage checking

    checkLength : Show a => List a -> ServerM (Vect n a)
    checkLength ls = maybeToEither (WrongArgumentLength n ls p )
                                   (exactLength n $ fromList ls)

||| Given an implementation of a path, return a list of function for each possible route
handleAllPaths : (state : Type) ->
                 (ref : IORef state) ->
                 (path : List (n ** PathComp n state)) ->
                 PathList path ->
                 List (Handler state)
handleAllPaths state ref [] [] = []
handleAllPaths state ref ((n ** comp) :: ts) (v :: vs)  =
       let paths =  handleAllPaths state ref ts vs
           path = stringSig ref n comp (makeParser comp)
                                   (pathCompToPrintRet comp)
                                   (convertPathFuncs v) in
           path :: paths

||| Given an implementation of a path, return a list of function for each possible route
forAllPaths : (state : Type) -> Show state =>
              (ref : IORef state) ->
              (path : Server.Path) ->
              Signature state path ->
              List (Handler state)
forAllPaths state ref path x = handleAllPaths state ref (toComponents state [] path)  x

||| Instanciate a new sever given a path and an implementation for it.
|||
||| @ path : The server's API as a Path.
||| @ impl : The server's implementation of the exposed API.
export partial
newServer : {state : Type} ->
            Show state =>
            (initial : state) ->
            (path : Server.Path) ->
            (impl : Signature state path) ->
            IO ()
newServer initial path impl = do
  ref <- newIORef initial
  server ref (forAllPaths state ref path impl)

{-
-}

module Engine

import Control.Monad.Converter
import Data.IORef
import Data.List1
import Data.Strings
import Data.Maybe
import Data.Either
import Data.Vect
import Data.IO.Logging
import Server
import Server.Utils
import URL
import Requests

import Debug.Trace

import System.File

-- A Handler attemps to parse the request and uses the current state to compute a response
Handler : Type -> Type
Handler state
        = state
       -> (components : List String)
       -> (queryItems : List (String, String))
       -> LogIO state (ServerM String)

-- Here the handlers are both parsing the string and returning the result of
-- the comutation as an encoded string. This is to void leaking the detail of
-- the dependency between the parsed type and the type of the handler.
export partial
server : {state : Type} -> (handlers : List (Handler state)) -> LogIO state ()
server handlers = Logging.do
    str <- awaitRequest
    log ("got request " ++ str)
    currentState <- getState
    let Just (path, body) = parseRequest str
      | _ => logVerbose ("Could not parse url " ++ str)
          *> server handlers
    logVerbose ("successfully parsed  request body " ++ show body)
    let path' = maybe path (snoc path) body
    result <- tryAll [] handlers currentState path' []
    logVerbose ("computed result " ++ show result)
    either (log . show) sendRequest result
    server handlers
  where
    -- Returns a handler that combines all handlers from a list by
    -- successively trying to apply them in order
    tryAll : List ServerError -> List (Handler state) -> Handler state
    tryAll errors [] state input query = pure $ Left $ Aggregate errors
    tryAll errors (f :: fs) state input query = do
      logVerbose "About to run handler"
      case !(f state input query) of
           Left err => do
             logVerbose "failed to handle, trying next handler"
             tryAll (err :: errors) fs state input query
           Right value => do
             logVerbose $ "handled value " ++ show value
             pure (Right value)

||| Returns a printing function for the return type of a given PathComp
total
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
            (length : Nat) ->
            (p : PathComp length state) ->
            (parsePath : (queryItems : List (String, String)) ->
                         (components : Vect length String) ->
                         ServerM (ParseArgs p)) ->
            (showResult : Ret p -> String) ->
            (handler : Args p -> Ret p) ->
            Handler state
stringSig n p parser printer handler state path query =
  let
      parsed = checkLength path >>= parser query -- have the arguments been parsed?
      handle = fromHandle p state handler -- given the arguments, print the result
      val = map handle parsed
      result = traverse
        (\v => do logVerbose "updateRet"
                  updateRet p v
                  let p = printer v
                  logVerbose ("ready to print \{p}")
                  pure ("Response: Ok \{p}")) val
  in result <* logVerbose "did compute result "
  where
    updateRet : {n : Nat} -> (path : PathComp n st) -> Ret path -> LogIO st ()
    updateRet (End rec (Query st) ret) {n=Z} y = logVerbose "nothing to update"
    updateRet (End rec (Update val st) ret) {n=1} (_, newState) =
      do logVerbose "writing IO Ref"
         writeState newState
         logVerbose "done writing"
    updateRet (Str _ p) {n=S n} y = updateRet p y
    updateRet (Tpe _ p) {n=S n} y = updateRet p y
    updateRet p _ = logVerbose ("cannot update, got path " ++ show p)

    checkLength : Show a => List a -> ServerM (Vect n a)
    checkLength ls = maybeToEither (WrongArgumentLength n ls p )
                                   (exactLength n $ fromList ls)

||| Given an implementation of a path, return a list of function for each possible route
export
handleAllPaths : (state : Type) ->
                 (path : List (n ** PathComp n state)) ->
                 PathList path ->
                 List (Handler state)
handleAllPaths state [] [] = []
handleAllPaths state ((n ** comp) :: ts) (v :: vs)  =
       let paths =  handleAllPaths state ts vs
           path = stringSig n
                            comp
                            (makeParser comp)
                            (pathCompToPrintRet comp)
                            (convertPathFuncs v)
        in path :: paths

||| Given an implementation of a path, return a list of function for each possible route
forAllPaths : (state : Type) -> Show state =>
              (path : Server.Path) ->
              Signature state path ->
              List (Handler state)
forAllPaths state path x = handleAllPaths state (toComponents state [] path)  x

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
  runLog Normal initial $ server (forAllPaths state path impl)

{-
-}

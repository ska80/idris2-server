module Data.IO.Logging

import Data.IORef
import System.File
import Requests

public export
data LogLevel

  -- No logging except for interative elements
  = Silent

  -- Only log errors
  | Error
  -- Log erros and warnings
  | Warning
  -- Log errors and normal messages
  | Normal
  -- Log everything
  | Verbose

export
Eq LogLevel where
  Silent == Silent = True
  Normal == Normal = True
  Verbose == Verbose = True
  _ == _ = False

interface Enum ty where
  value : ty -> Nat

Enum LogLevel where
  value Silent = 0
  value Error = 1
  value Warning = 2
  value Normal = 3
  value Verbose = 4

export
Ord LogLevel where
  compare left right = compare (value left) (value right)

||| A monad that logs events, carries an internal state and communicate with the outside world
||| though a network connection
||| The internal state is used to model state updates on the server
export
data LogIO : Type -> Type -> Type where
  ||| Create a value
  Pure : val -> LogIO st val
  ||| Receive a request from the network, typically on a socket or on STDOut
  Read : LogIO st Request
  ||| Send a request on the network, typically on a socket or on STDOut
  Write : String -> LogIO st ()
  ||| Get the interal state
  ReadState : LogIO st st
  ||| Overwrite the internal state
  WriteState : st -> LogIO st ()
  ||| Change the log level that we print
  ChLvl : (lvl : LogLevel) -> LogIO st ()
  ||| Write a log
  Log : (lvl : LogLevel) -> String -> LogIO st ()
  ||| Sequence two LogIO operations
  Bind : LogIO st ty -> (ty -> LogIO st sy) -> LogIO st sy

export %inline
pure : val -> LogIO st val
pure = Pure

export %inline
log : String -> LogIO st ()
log = Log Normal

export %inline
logVerbose : String -> LogIO st ()
logVerbose = Log Verbose

export %inline
logError : String -> LogIO st ()
logError = Log Error

export %inline
awaitRequest : LogIO st Request
awaitRequest = Read

export %inline
sendRequest : String -> LogIO st ()
sendRequest = Write

export %inline
getState : LogIO st st
getState = ReadState

export %inline
writeState : st -> LogIO st ()
writeState = WriteState

export %inline
(>>=) : LogIO st ty -> (ty -> LogIO st sy) -> LogIO st sy
(>>=) = Bind

export %inline
(>>) : LogIO st a -> LogIO st b -> LogIO st b
(>>) x y = Bind x (const y)

export
Functor (LogIO st) where
  map f (Pure x) = Pure (f x)
  map f Read = Bind Read (pure . f)
  map f (Write x) = Bind (Write x) (pure . f)
  map f ReadState = Bind ReadState (pure . f)
  map f (WriteState x) = Bind (WriteState x) (pure . f)
  map f (ChLvl lvl) = Bind (ChLvl lvl) (pure . f)
  map f (Log lvl x) = Bind (Log lvl x) (pure . f)
  map f (Bind x g) = Bind (Bind x g) (pure . f)

export
Applicative (LogIO st) where
  pure = Logging.pure
  (<*>) f (Pure x) = map (\g => g x) f
  (<*>) f Read = Bind f (\f' => Bind Read (Pure . f'))
  (<*>) f (Write x) = Bind f (\f' => Bind (Write x) (Pure . f'))
  (<*>) f ReadState = Bind f (\f' => Bind ReadState (Pure . f'))
  (<*>) f (WriteState x) = Bind f (\f' => Bind (WriteState x) (Pure . f'))
  (<*>) f (ChLvl lvl) = Bind f (\f' => Bind (ChLvl lvl) (Pure . f'))
  (<*>) f (Log lvl x) = Bind f (\f' => Bind (Log lvl x) (Pure . f'))
  (<*>) f (Bind x g) = Bind f (\f' => Bind (Bind x g) (Pure . f'))

export
Monad (LogIO st) where
  (>>=) ma ct = Bind ma ct
  join mma = mma >>= \x => x

parameters (lvl : IORef LogLevel) (state : IORef st)
  execLog : LogIO st ty -> IO ty
  execLog (Pure x) = pure x
  execLog Read =
    let str = !getLine
        Just req = parseRequest str
      | _ => execLog $
             logError ("Could not parse request " ++ str)
          *> log "supported requests:"
          *> log "GET url/to/resource"
          *> log "POST url/to/resource *body*"
          *> Read
     in pure req
  execLog (Write x) = putStrLn x
  execLog (ChLvl x) = writeIORef lvl x
  execLog ReadState = readIORef state
  execLog (WriteState st) = writeIORef state st
  execLog (Log loglvl y) =
    when (!(readIORef lvl) >= loglvl)
         (putStrLn y *> fflush stdout)
  execLog (Bind x f) =
    execLog x >>= execLog . f

||| Run the LogIO monad, given an initial state, a log level to print and a LogIO action
||| this will run the program in the IO Monad
export
runLog : (lvl : LogLevel) -> (initial : st) -> LogIO st ty -> IO ty
runLog lvl initial prog = execLog !(newIORef lvl) !(newIORef initial) prog

module Data.IO.Logging

import Data.IORef
import System.File

public export
data LogLevel = Silent | Normal | Verbose

export
Eq LogLevel where
  Silent == Silent = True
  Normal == Normal = True
  Verbose == Verbose = True
  _ == _ = False

export
Ord LogLevel where
  compare Silent Silent = EQ
  compare Silent _ = LT
  compare Normal Silent = GT
  compare Normal Normal = EQ
  compare Normal Verbose = GT
  compare Verbose Verbose = EQ
  compare Verbose _ = GT

export
data LogIO : Type -> Type -> Type where
  Pure : val -> LogIO st val
  Read : LogIO st String -- readfrom socket/STDIN
  Write : String -> LogIO st () -- write to socket/STDOUt
  ReadState : LogIO st st
  WriteState : st -> LogIO st ()
  ChLvl : (lvl : LogLevel) -> LogIO st ()
  Log : (lvl : LogLevel) -> String -> LogIO st ()
  Bind : LogIO st ty -> (ty -> LogIO st sy) -> LogIO st sy

export %inline
pure : val -> LogIO st val
pure = Pure

export %inline
log : String -> LogIO st ()
log x = Log Normal x

export %inline
logVerbose : String -> LogIO st ()
logVerbose x = Log Verbose x

export %inline
awaitRequest : LogIO st String
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
  execLog Read = getLine
  execLog (Write x) = putStrLn x
  execLog (ChLvl x) = writeIORef lvl x
  execLog ReadState = readIORef state
  execLog (WriteState st) = writeIORef state st
  execLog (Log loglvl y) =
    when (!(readIORef lvl) >= loglvl)
         (putStrLn y *> fflush stdout)
  execLog (Bind x f) =
    execLog x >>= execLog . f

export
runLog : (lvl : LogLevel) -> (initial : st) -> LogIO st ty -> IO ty
runLog lvl initial prog = execLog !(newIORef lvl) !(newIORef initial) prog

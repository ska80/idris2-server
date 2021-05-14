module Control.Monad.Converter

import Control.Monad.State
import Data.IORef

infix 4 =*>

public export
interface (=*>) (0 m, n : Type -> Type) where
  lift : m a -> n a

public export
implementation (=*>) m m where
  lift = id

||| Given an IO Ref that stores the state, we can convert from State to IO
public export
(ref : IORef stateType) => (=*>) (State stateType) IO where
  lift op = do st <- readIORef ref
               let (newState, value) = runState st op
               writeIORef ref newState
               pure value

public export
(=*>) Identity IO where
  lift (Id v) = pure v




module Main

import Server
import Engine
import EDSL
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat

%hide Prelude.(/)

infixr 5 /

data T1 = T

Show T1 where
  show T = "T"

API : Path
API = "path" / "to" / "resource" / Returns T1 Get

SimpleAPI : Signature () API
SimpleAPI = [\_ => T]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer () API SimpleAPI


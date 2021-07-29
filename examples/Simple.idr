module Main

import Server
import Server.EDSL.Servant
import Data.Nat

%hide Prelude.(/)

infixr 5 /

data T1 = T

Show T1 where
  show T = "T"

Display T1 where
  display = "T1"

Default T1 where
  def = T

API : Path
API = "path" / "to" / "resource" / Returns T1 Get

SimpleAPI : Signature () API
SimpleAPI = [\_ => T]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer Normal () API SimpleAPI


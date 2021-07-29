module Main

import Server
import Server.EDSL.Servant
import Data.IORef
import Data.Nat

%hide Prelude.(/)
infixr 5 /

API : Path
API = "path" / "to" / "resource" / Returns Int Get

SimpleAPI : Signature () API
SimpleAPI = [const 1337]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer Normal () API SimpleAPI


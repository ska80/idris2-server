module Main

import Server
import Engine
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat


API : Path
API = Cap "left" Int // Cap "right" Int // Returns Int Get Ok

SimpleAPI : Signature (Identity) API
SimpleAPI = [\x, y => pure (x + y)]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer API SimpleAPI


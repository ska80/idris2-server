module Main

import Server
import Engine
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat


API : Path
API = "path" // "to" // "resource" // Returns () Get Ok

SimpleAPI : Signature (Identity) API
SimpleAPI = [pure ()]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer API SimpleAPI


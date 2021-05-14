module Main

import Server
import Engine
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat

%ambiguity_depth 4

API : Path
API = Split [
  Cap "left" Int // Cap "right" Int // "add" // Returns Int Get Ok,
  Cap "left" Int // Cap "right" Int // "min" // Returns Int Get Ok,
  Cap "left" Int // Cap "right" Int // "mul" // Returns Int Get Ok,
  Cap "left" Int // Cap "right" Int // "div" // Returns Int Get Ok]

SimpleAPI : Signature (Identity) API
SimpleAPI = [\x, y => pure (x + y)
            ,\x, y => pure (x - y)
            ,\x, y => pure (x * y)
            ,\x, y => pure (x `div` y)]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer API SimpleAPI


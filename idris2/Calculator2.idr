module Main

import Server
import Engine
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat

%ambiguity_depth 4

API : Path
API =
  Cap "left" Int // Cap "right" Int // Split
      [ "add" // Returns Int Get Ok
      , "min" // Returns Int Get Ok
      , "mul" // Returns Int Get Ok
      , "div" // Returns Int Get Ok]

CalcAPI : Signature (Identity) API
CalcAPI = [\x, y => pure (x + y)
            ,\x, y => pure (x - y)
            ,\x, y => pure (x * y)
            ,\x, y => pure (x `div` y)]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer API CalcAPI


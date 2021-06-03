module Main

import Server
import Engine
import EDSL
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat

%ambiguity_depth 4

%hide Prelude.(/)

infixr 5 /

API : Path
API = Split [
  Cap "left" Int / Cap "right" Int / "add" / Returns Int Get,
  Cap "left" Int / Cap "right" Int / "min" / Returns Int Get,
  Cap "left" Int / Cap "right" Int / "mul" / Returns Int Get,
  Cap "left" Int / Cap "right" Int / "div" / Returns Int Get]

SimpleAPI : Signature () API
SimpleAPI = [\x, y, () => x + y
            ,\x, y, () => x - y
            ,\x, y, () => x * y
            ,\x, y, () => x `div` y]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer () API SimpleAPI


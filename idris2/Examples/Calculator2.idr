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
API =
  Cap "left" Int / Cap "right" Int / Split
      [ "add" / Returns Int Get
      , "min" / Returns Int Get
      , "mul" / Returns Int Get
      , "inc" / Returns Int Get
      , "div" / Returns Int Get]

CalcAPI : Signature () API
CalcAPI = [\x, y, () => x + y
          ,\x, y, () => x - y
          ,\x, y, () => x * y
          ,\x, y, () => x + y + 1
          ,\x, y, () => x `div` y]

-- -- In order to run the server we need to supply it with an initial state
-- -- which will be stored as an IORef
-- main : IO ()
-- main = newServer () API CalcAPI


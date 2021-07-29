module Main

import Server
import Server.EDSL.Servant
import Control.Monad.State

%hide Prelude.(/)

infixr 5 /

API : Path
API = Cap "left" Int / Cap "right" Int / Split [
   "add" / Returns Int Get,
   "min" / Returns Int Get,
   "mul" / Returns Int Get,
   "div" / Returns Int Get]

SimpleAPI : Signature () API
SimpleAPI = [\x, y, () => x + y
            ,\x, y, () => x - y
            ,\x, y, () => x * y
            ,\x, y, () => x `div` y]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer Normal () API SimpleAPI


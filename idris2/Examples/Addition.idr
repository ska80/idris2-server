module Examples.Addition

import Server
import Engine
import EDSL
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat

%hide Prelude.(/)

infixr 5 /

API : Path
API = Cap "left" Int / Cap "right" Int / Returns Int Get

SimpleAPI : Signature () API
SimpleAPI = [\x, y, () => x + y]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer () API SimpleAPI


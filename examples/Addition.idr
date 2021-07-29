module Addition

import Server
import Server.EDSL.Servant
import Data.IO.Logging

%hide Prelude.(/)

infixr 5 /

API : Path
API = Cap "left" Int / Cap "right" Int / Returns Int Get

SimpleAPI : Signature () API
SimpleAPI = [\x, y, () => x + y]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = newServer Error () API SimpleAPI


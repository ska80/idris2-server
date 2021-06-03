module Examples.IOT

import Server
import Engine
import EDSL

%hide Prelude.(/)
infixr 5 /

record HomeState where
  constructor MkHomeState
  boiler : Bool
  lights : (Double, Double, Double)


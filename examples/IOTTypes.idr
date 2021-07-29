module IOTTypes

import Optics
import Data.String.Parser
import Server

public export
Lights : Type
Lights = (Double, Double, Double)

public export
record HomeState where
  constructor MkHomeState
  boiler : Bool
  lights : Lights

export
lightsLens : Lens Lights    Lights
                  HomeState (Lights, HomeState)
lightsLens = MkLens lights (\(st, v) => (v, record { lights = v } st))

export
HasParser HomeState where
  partialParse = [| MkHomeState partialParse partialParse |]

export
Show HomeState where
  show (MkHomeState b l) = "MkHomeState \{show b} \{show l}"

export
boilerLens : Lens Bool Bool HomeState (Bool, HomeState)
boilerLens = MkLens boiler (\(st, v) => (v, record { boiler = v } st))

export
fstLens : Lens a a (a, b) (a, b)
fstLens = MkLens fst (\((_, b), new) => (new, b))

export
sndLens : Lens b b (a, b) (a, b)
sndLens = MkLens snd (\((a, _), new) => (a, new))

export
trdLens : Lens c c (a, b, c) (a, b, c)
trdLens = sndLens `compose` sndLens

export
initialState : HomeState
initialState = MkHomeState False (0,0,0)

module Examples.IOT

import Server
import Engine
import EDSL
import Optics
import Data.String.Parser

%hide Prelude.(/)

-- %ambiguity_depth 5

infixr 5 /

Lights : Type
Lights = (Double, Double, Double)

record HomeState where
  constructor MkHomeState
  boiler : Bool
  lights : Lights

Show HomeState where

implementation HasParser HomeState where
  partialParse = [| MkHomeState partialParse partialParse |]

boilerLens : Lens Bool Bool HomeState HomeState
boilerLens = MkLens boiler (\(st, v) => record { boiler = v } st)

lightsLens : Optic Fn (Double, Double, Double) (Double, Double, Double)
                  HomeState HomeState
lightsLens = lens2Pro {p=Fn} $ MkLens lights (\(st, v) => record { lights = v } st)

fstLens : Optic Fn a a (a, b) (a, b)
fstLens = lens2Pro {p=Fn} $ MkLens fst (\((_, b), new) => (new, b))

sndLens : Optic Fn b b (a, b) (a, b)
sndLens = lens2Pro {p=Fn} $ MkLens snd (\((a, _), new) => (a, new))

trdLens : Optic Fn c c (a, b, c) (a, b, c)
trdLens = sndLens . sndLens

kitchenLight : Optic Fn Double Double HomeState HomeState
kitchenLight = lightsLens . fstLens

bedroomLight : Optic Fn Double Double HomeState HomeState
bedroomLight = lightsLens . sndLens . fstLens

livingroomLight : Optic Fn Double Double HomeState HomeState
livingroomLight = lightsLens . trdLens

HomeBoiler : Path
HomeBoiler = "boiler" / Resource Bool HomeState

HomeLights : Path
HomeLights = "lights" / Resource Lights HomeState

HomeAPI : Path
HomeAPI = Split ["boiler" / Returns Bool Get,
                 "boiler" / Returns Bool (Post Bool),
                 "lights" / Returns Lights Get,
                 "lights" / Returns Lights (Post Lights)]

HomeImpl : Signature HomeState HomeAPI
HomeImpl = ?a :: ?b


-- main : IO ()
-- main = newServer

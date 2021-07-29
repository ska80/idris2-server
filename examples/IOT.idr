module IOT

import Server
import Server.EDSL.Lenses
import Server.EDSL.Servant
import Text.PrettyPrint.PrettyPrinter
import Optics
import Server.Documentation
import Data.String
import Data.String.Parser
import IOTTypes

{-
-- servant-like implementation
SimpleAPI : Path
SimpleAPI = Split [ "boiler" / Returns Bool Get
                  , "boiler" / Returns Bool (Post Bool)
                  , "lights" / Returns Lights Get
                  , "lights" / Returns Lights (Post Lights)]

-- implementation uses lenses
simpleServer : Signature HomeState SimpleAPI
simpleServer = [ boilerLens.get
               , fixup boilerLens.set
               , lightsLens.get
               , fixup lightsLens.set ]

main : IO ()
main = newServer Normal initialState SimpleAPI simpleServer

-}







{-
-- inlining lenses
NaivePath : ServerTree HomeState
NaivePath = Fork [ Wrap ("boiler" / Ret Bool HomeState Get :|:
                 boilerLens.get)
                 , Wrap ("boiler" / Ret Bool HomeState (Post Bool)  :|:
                 fixup boilerLens.set)]

main : IO ()
main = runServer Normal NaivePath initialState
-}








{-
-- refactoring the common parts into a common prefix
RefactoredPath : ServerTree HomeState
RefactoredPath = (Prefix "boiler" (Fork [ Wrap (Ret Bool HomeState Get :|: boilerLens.get)
                                        , Wrap (Ret Bool HomeState (Post Bool)  :|: fixup boilerLens.set)]))

main : IO ()
main = runServer Normal RefactoredPath initialState
-}









{-
main : IO ()
main = runServer Normal (Prefix "boiler" (ResourceLens boilerLens)) initialState
-}







{-

LensPath : ServerTree HomeState
LensPath = Prefix "boiler" (ResourceLens boilerLens)

LightsPath : ServerTree HomeState
LightsPath = Prefix "lights" (ResourceLens lightsLens)

-- Extended the server with lights
FullPath : ServerTree HomeState
FullPath = Prefix "home" (Fork [ LensPath
                               , LightsPath])

main : IO ()
main = runServer Normal FullPath initialState
-}









{-
LensPath : ServerTree HomeState
LensPath = Prefix "boiler" (ResourceLens boilerLens)

LightsPath : ServerTree HomeState
LightsPath = Prefix "lights" (ResourceLens lightsLens)

KitchenLights : ServerTree HomeState
KitchenLights = (LightsPath ~/ "kitchen") {lens=lightsLens} fstLens

LivingLights : ServerTree HomeState
LivingLights = (LightsPath ~/ "living") {lens=lightsLens} (fstLens `compose` sndLens)

BathroomLights : ServerTree HomeState
BathroomLights = (LightsPath ~/ "bathroom") {lens=lightsLens} trdLens

ExtendedPath : ServerTree HomeState
ExtendedPath =
  Prefix "home" (Fork [ LensPath
                      , Prefix "lights" (GetLens lightsLens)
                      , KitchenLights
                      , LivingLights
                      , BathroomLights])

-- print documentation
main : IO ()
main = printLn (docsFromTree ExtendedPath)


-- main : IO ()
-- main = runServer Normal ExtendedPath initialState
-}

LensPath : ServerTree HomeState
LensPath = Prefix "boiler" (ResourceLens boilerLens)

LightsPath : ServerTree HomeState
LightsPath = Prefix "lights" (ResourceLens lightsLens)

ExtendedPath : ServerTree HomeState
ExtendedPath =
  Prefix "home" (Fork [ LensPath
                      , Prefix "lights" (GetLens lightsLens)
                      , (LightsPath ~/ "bathroom") {lens=lightsLens} trdLens
                      -- , (((LightsPath ~/ "living+bathroom") {lens=lightsLens} sndLens)
                      --                 ~/ "living") {lens=(composeStates sndLens lightsLens)} fstLens
                      , ((LightsPath ~/ "living") {lens=lightsLens} (fstLens `compose` sndLens))
                      , (LightsPath ~/ "kitchen") {lens=lightsLens} fstLens])

-- print documentation
main : IO ()
main = printLn (docsFromTree ExtendedPath)













SimpleAPI' : Path
SimpleAPI' = Split [ "boiler" / Returns Bool Get
                   , "boiler" / Returns Bool (Post Bool)
                   , "lights" / Returns Lights Get
                   , "lights" / Returns Lights (Post Lights)
                   , "lights" / Split [ "kitchen" / Returns Double Get
                                      , "kitchen" / Returns Double (Post Double)
                                      , "living" / Returns Double Get
                                      , "living" / Returns Double (Post Double)
                                      , "bathroom" / Returns Double Get
                                      , "bathroom" / Returns Double (Post Double)
                                      ]]



-- implementation uses lenses
simpleServer : Signature HomeState SimpleAPI'
simpleServer = [ boilerLens.get
               , fixup boilerLens.set
               , lightsLens.get
               , fixup lightsLens.set
               , ?fn1
               , ?fn2
               , ?fn3
               , ?fn4
               , ?fn5
               , ?fn6
               ]


{-
-}

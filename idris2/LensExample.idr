module LensExample

import EDSL
import Server
import Engine
import Optics
import Data.IORef
import Data.IO.Logging
import Data.String
import Data.String.Parser
import Text.PrettyPrint.PrettyPrinter
import Documentation as Doc

%hide Prelude.(/)
infixr 5 /
infixr 4 ~/

fixup : ((a, b) -> c) -> b -> a -> c
fixup f x y = f (y, x)

Lights : Type
Lights = (Double, Double, Double)

record HomeState where
  constructor MkHomeState
  boiler : Bool
  lights : Lights

initial : HomeState
initial = MkHomeState False (0,0,0)

Show HomeState where
  show (MkHomeState b l) = "MkHomeState \{show b} \{show l}"

implementation HasParser HomeState where
  partialParse = [| MkHomeState partialParse partialParse |]

boilerLens : Lens Bool Bool HomeState (Bool, HomeState)
boilerLens = MkLens boiler (\(st, v) => (v, record { boiler = v } st))

lightsLens : Lens Lights Lights
                  HomeState (Lights, HomeState)
lightsLens = MkLens lights (\(st, v) => (v, record { lights = v } st))

-- fstLens : Optic Fn a a (a, b) (a, b)
-- fstLens = lens2Pro {p=Fn} $ MkLens fst (\((_, b), new) => (new, b))

fstLens : Lens a a (a, b) (a, b)
fstLens = MkLens fst (\((_, b), new) => (new, b))

ffst : Lens a a (a, b, c) (a, b, c)
ffst = MkLens fst ?set

sndLens : Lens b b (a, b) (a, b)
sndLens = MkLens snd (\((a, _), new) => (a, new))

trdLens : Lens c c (a, b, c) (a, b, c)
trdLens = sndLens `compose` sndLens

--kitchenLight : Optic Fn Double Double HomeState HomeState
--kitchenLight = lightsLens . fstLens
--
--bedroomLight : Optic Fn Double Double HomeState HomeState
--bedroomLight = lightsLens . sndLens . fstLens
--
--livingroomLight : Optic Fn Double Double HomeState HomeState
--livingroomLight = lightsLens . trdLens

GetLights : PathComp 1 HomeState
GetLights = Str "lights" $ End Nothing (Query HomeState) Lights

implGetLights : PathCompToType GetLights
implGetLights = lightsLens.get

||| Given a path component, extend it with a lens
ExtendPath : {newFocus : Type}
          -> (path : PathComp n st)
          -> Documented newFocus
          => Lens newFocus newFocus (RetTy path) (RetTy path)
          -> String
          -> PathComp (S n) st
ExtendPath (End q update ret) lens comp =
  Str comp $ End q update newFocus
ExtendPath (Str z w) x y = Str z (ExtendPath w x y)
ExtendPath (Tpe t z) x y = Tpe t (ExtendPath z x y)

||| Given a path component and a lens, derive the implementation for the extended path
ExtendComponent : {newFocus : Type} -> (path : PathComp n st)
               -> (impl : PathCompToType path)
               -> Documented newFocus
               => (lens : Lens newFocus newFocus (RetTy path) (RetTy path))
               -> (comp : String)
               -> PathCompToType (ExtendPath path lens comp)
ExtendComponent (End Nothing (Query st) ret) impl lens comp = lens.get . impl
ExtendComponent (End Nothing (Update v st) ret) impl lens comp =
  \v => mapFst lens.get . (impl v)
ExtendComponent (End (Just x) (Query st) ret) impl lens comp =
  \rec => lens.get . (impl rec)
ExtendComponent (End (Just x) (Update v st) ret) impl lens comp =
  \rec, v => mapFst lens.get . (impl rec v)
ExtendComponent (Str str ps) impl lens comp =
  ExtendComponent ps impl lens comp
ExtendComponent (Tpe ty ps) impl lens comp = \arg =>
  ExtendComponent ps (impl arg) lens comp

infixr 2 :|:

-- An implementation for a given path parameterised over the state
data ServerImpl : Type -> Type where
  (:|:) : {n : Nat} -> (path : PathComp n st) -> (impl : PathCompToType path) -> ServerImpl st

insertPrefix : String -> ServerImpl st -> ServerImpl st
insertPrefix pre (path :|: impl) = Str pre path :|: impl

data ServerTree : Type -> Type where
  Wrap : ServerImpl st -> ServerTree st
  Prefix : String -> ServerTree st -> ServerTree st
  Fork : List (ServerTree st) -> ServerTree st

Ret : (ret : Type) -> Documented ret => (st : Type) -> Show st => (verb : Verb) ->
      PathComp (case verb of Get => 0; (Post _) => 1) st
Ret ret st Get = End Nothing (Query st) ret
Ret ret st (Post arg) = End Nothing (Update arg st) ret

-- fc for "focus" and "st" fot "state"
ResourceLens : {fc, st : Type} -> Documented fc => HasParser fc => Show st => Lens fc fc st (fc, st) -> ServerTree st
ResourceLens lens = Fork
  [ Wrap (Ret fc st Get :|: lens.get)
  , Wrap (Ret fc st (Post fc) :|: fixup lens.set)
  ]

interface EDSL ty where
  (/) : ty -> PathComp n st -> PathComp (S n) st

data TyArg : Type where
  Ty : (ty : Type) -> HasParser ty => Documented ty => TyArg

implementation EDSL TyArg where
  (Ty ty) / ps = Tpe ty ps

implementation EDSL String where
  str / ps = Str str ps

data IsResource : ServerTree st -> (fc, st : Type) -> Lens fc fc st (fc, st) -> Type where
  IsPrefix : IsResource ts fc st lens -> IsResource (Prefix p ts) fc st lens
  FoundResource : {fc, st : Type} -> Documented fc => HasParser fc => Show st => {lens : Lens fc fc st (fc, st)} ->
                                                     {res : ServerTree st} ->
                                                     {same : res === ResourceLens lens} ->
                  IsResource res fc st lens

composeStates : Lens newFc newFc fc fc -> Lens fc fc st (fc, st) -> Lens newFc newFc st (newFc, st)
composeStates x y = MkLens (x.get . y.get) (\(oldSt, newVal) =>
                        (newVal , snd $ y.set (oldSt, x.set (y.get oldSt, newVal))))

(~/) : {newFc : Type} -> (tree : ServerTree st) -> {auto res : IsResource tree fc st lens} ->
       Documented newFc => HasParser newFc =>
       String -> Lens newFc newFc fc fc -> ServerTree st
(~/) (Prefix p ts) {res = (IsPrefix x)} comp newLens =
  Prefix p ((~/) ts {res=x} comp newLens)
(~/) tree {res = FoundResource {lens = l1} {same = same}} comp l2 =
  Prefix comp (ResourceLens {fc=newFc} (composeStates l2 l1))

-- Refactoring a resource as a lens
LensPath : ServerTree HomeState
LensPath = Prefix "boiler" (ResourceLens boilerLens)

LightsPath : ServerTree HomeState
LightsPath = Prefix "lights" (ResourceLens lightsLens)

KitchenLights : ServerTree HomeState
KitchenLights = (LightsPath ~/ "kitchen") {lens=lightsLens} fstLens

LivingLights : ServerTree HomeState
LivingLights = (LightsPath ~/ "living") {lens=lightsLens} sndLens

BathroomLights : ServerTree HomeState
BathroomLights = (LightsPath ~/ "bathroom") {lens=lightsLens} trdLens

ExtendedPath : ServerTree HomeState
ExtendedPath =
  Prefix "home" (Fork [ LensPath
                      , LightsPath
                      , KitchenLights
                      , BathroomLights
                      , LivingLights])

SimpleAPI : Path
SimpleAPI = Split [ "boiler" / Returns Bool Get
                  , "boiler" / Returns Bool (Post Bool)
                  , "lights" / Returns Lights Get
                  , "lights" / Returns Lights (Post Lights)]

-- HomeAPI = (MkResource "home" HomeState) -< [ MkExt "boiler" BoilerLens
--                                            , MkExt "lights" LightsLens -< [ MkExt "kitchen" FstLens
--                                                                           , MkExt "living" SndLens
--                                                                           , MkExt "bedroom" TrdLens[
--                                            ]

simpleServer : Signature HomeState SimpleAPI
simpleServer = [ boilerLens.get
               , fixup boilerLens.set
               , lightsLens.get
               , fixup lightsLens.set ]

-- naive boiler
NaivePath : ServerTree HomeState
NaivePath = Fork [ Wrap ("boiler" / Ret Bool HomeState Get :|: boilerLens.get)
                 , Wrap ("boiler" / Ret Bool HomeState (Post Bool)  :|: fixup boilerLens.set)]

-- refactoring the common parts into a common prefix
RefactoredPath : ServerTree HomeState
RefactoredPath = (Prefix "boiler" (Fork [ Wrap (Ret Bool HomeState Get :|: boilerLens.get)
                                        , Wrap (Ret Bool HomeState (Post Bool)  :|: fixup boilerLens.set)]))


-- Extended the server with lights
FullPath : ServerTree HomeState
FullPath = Prefix "home" (Fork [ LensPath
                               , LightsPath])


fromServerTree : ServerTree st -> (path : List (n ** PathComp n st) ** PathList path)
fromServerTree = ServerToPathComp . serverToPaths
  where
  ServerToPathComp : List (ServerImpl st) -> (path : List (n ** PathComp n st) ** PathList path)
  ServerToPathComp [] = ([] ** [])
  ServerToPathComp ((path :|: impl) :: xs) =
    let (path' ** imp') = ServerToPathComp xs in ((_ ** path) :: path' ** impl :: imp')

  serverToPaths : ServerTree st -> List (ServerImpl st)
  serverToPaths (Wrap x) = [x]
  serverToPaths (Prefix str paths) =
    map (insertPrefix str) (serverToPaths paths)
  serverToPaths (Fork xs) = xs >>= serverToPaths

partial
runServer : {st : Type} -> ServerTree st -> (initial : st) -> IO ()
runServer api initial =
  let (paths ** impl) = fromServerTree api in
  runLog Silent initial $ server (handleAllPaths st paths impl)

docsFromTree : ServerTree st -> Doc String
docsFromTree tree = let (path ** _) = fromServerTree tree in generateDocs (map (, Nothing) path)

main : IO ()
main = printLn (docsFromTree ExtendedPath)

-- TODO:
--   - [x] Extend paths with lenses
--   - [x] re-implement every server as lenses (if possible?)
--   - [ ] Intanciate server
--   - [ ] update the syntax
--   - [ ] implement more examples

runSimple : IO ()
runSimple = newServer initial SimpleAPI simpleServer
{-
-}

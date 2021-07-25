module Server.EDSL.Lenses

import Server
import Optics
import Data.IORef
import Data.IO.Logging
import Data.String
import Data.String.Parser
import Text.PrettyPrint.PrettyPrinter
import Server.Documentation as Doc

%hide Prelude.(/)
infixr 5 /
infixr 4 ~/

public export
fixup : ((a, b) -> c) -> b -> a -> c
fixup f x y = f (y, x)

||| Given a path component, extend it with a lens
public export
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
public export
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

||| An endpoint as a PathComp along with its implementation
public export
data ServerImpl : Type -> Type where
  (:|:) : {n : Nat} -> (path : PathComp n st) -> (impl : PathCompToType path) -> ServerImpl st

insertPrefix : String -> ServerImpl st -> ServerImpl st
insertPrefix pre (path :|: impl) = Str pre path :|: impl

||| This data captures the structure of an API as a tree. Path components can only be strings
||| The tree cannot contain captures
public export
data ServerTree : Type -> Type where
  Wrap : ServerImpl st -> ServerTree st
  Prefix : String -> ServerTree st -> ServerTree st
  Fork : List (ServerTree st) -> ServerTree st

public export
Ret : (ret : Type) -> Documented ret => (st : Type) -> Show st => (verb : Verb) ->
      PathComp (case verb of Get => 0; (Post _) => 1) st
Ret ret st Get = End Nothing (Query st) ret
Ret ret st (Post arg) = End Nothing (Update arg st) ret

||| Create a new resource from a lens, that is both a GET and POST endpoint using the lens as it's implementation
public export
-- fc for "focus" and "st" for "state"
ResourceLens : {fc, st : Type} -> Documented fc => HasParser fc => Show st => Lens fc fc st (fc, st) -> ServerTree st
ResourceLens lens = Fork
  [ Wrap (Ret fc st Get :|: lens.get)
  , Wrap (Ret fc st (Post fc) :|: fixup lens.set)
  ]

||| Use the `get` part of a lens as a GET request
export
GetLens : {fc, st : Type} -> Documented fc => HasParser fc => Show st => Lens fc _ st _ -> ServerTree st
GetLens lens = Wrap (Ret fc st Get :|: lens.get)

||| Use the `set` part of a lens as a POST request
export
PostLens : {fc, st : Type} -> Documented fc => HasParser fc => Show st => Lens fc fc st (fc, st) -> ServerTree st
PostLens lens = Wrap (Ret fc st (Post fc) :|: fixup lens.set)

public export
interface EDSL ty where
  (/) : ty -> PathComp n st -> PathComp (S n) st

public export
data TyArg : Type where
  Ty : (ty : Type) -> HasParser ty => Documented ty => TyArg

public export
implementation EDSL TyArg where
  (Ty ty) / ps = Tpe ty ps

public export
implementation EDSL String where
  str / ps = Str str ps

||| A proof that a given server reprensents a resource
public export
data IsResource : ServerTree st -> (fc, st : Type) -> Lens fc fc st (fc, st) -> Type where
  IsPrefix : IsResource ts fc st lens -> IsResource (Prefix p ts) fc st lens
  FoundResource : {fc, st : Type} ->
                  Documented fc =>
                  HasParser fc =>
                  Show st =>
                  {lens : Lens fc fc st (fc, st)} ->
                  {res : ServerTree st} ->
                  {same : res === ResourceLens lens} ->
                  IsResource res fc st lens

||| Composition of a stateful lens and a regular lens
||| The first lens focuses on some value of the state, and the resulting lens
||| accesses and updates the nested value inside the state
public export
composeStates : Lens newFc newFc fc fc -> Lens fc fc st (fc, st) -> Lens newFc newFc st (newFc, st)
composeStates x y = MkLens (x.get . y.get) (\(oldSt, newVal) =>
                        (newVal , snd $ y.set (oldSt, x.set (y.get oldSt, newVal))))

||| This operator extends an existing server provided it's been implemented as a resource
public export
(~/) : {newFc : Type} ->
       (tree : ServerTree st) ->
       {auto res : IsResource tree fc st lens} ->
       Documented newFc => HasParser newFc =>
       String -> Lens newFc newFc fc fc -> ServerTree st
(~/) (Prefix p ts) {res = (IsPrefix x)} comp newLens =
  Prefix p ((~/) ts {res=x} comp newLens)
(~/) tree {res = FoundResource {lens = l1} {same = same}} comp l2 =
  Prefix comp (ResourceLens {fc=newFc} (composeStates l2 l1))

||| Creates a PathList from a ServerTree
export
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

partial export
runServer : {st : Type} -> ServerTree st -> (initial : st) -> IO ()
runServer api initial =
  let (paths ** impl) = fromServerTree api in
  runLog Normal initial $ server (handleAllPaths st paths impl)

export
docsFromTree : ServerTree st -> Doc String
docsFromTree tree = let (path ** _) = fromServerTree tree in generateDocs (map (, Nothing) path)


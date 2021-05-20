module Lens

import Data.Vect
import Products

infixl 5 :+:
infixl 6 &&

(:+:) : Type -> Type -> Type
(:+:) = Either

--     ┌──────┐
-- s >─┤      ├─> a
--     │      │
-- t <─┤      ├─< b
--     └──────┘
public export
record Lens (a, b, s, t : Type) where
  constructor MkLens
  get : s -> a
  set : s :*: b -> t

public export
record Prism (a, b, s, t: Type) where
  constructor MkPrism
  match : s -> Either t a
  build : b -> t

public export
record Adapter (a, b, s, t : Type) where
  constructor MkApt
  from : s -> a
  to : b -> t

public export
record Traversal (a, b, s, t : Type) where
  constructor MkTrav
  extract : s -> (n ** (Vect n a, Vect n b -> t))

interface Profunctor p where
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'

interface Profunctor p => Cartesian p where
  first : p a b -> p (a :*: c) (b :*: c)
  second : p a b -> p (c :*: a) (c :*: b)

interface Profunctor p => CoCartesian p where
  left : p a b -> p (a :+: c) (b :+: c)
  right : p a b -> p (c :+: a) (c :+: b)

interface Profunctor p => Monoidal p where
  empty : p () ()
  (&&) : p a b -> p c d -> p (a :*: c) (b :*: d)

implementation Profunctor (Lens a b) where
  dimap f g (MkLens get set)  = MkLens (get . f) (g . set . mapFst f)

implementation Cartesian (Lens a b) where
  first (MkLens get set) = MkLens (get . fst) (\x => (set (fst (fst x), snd x), snd (fst x)))
  second (MkLens get set) = MkLens (get . snd) (\x => (fst (fst x), set (snd (fst x), snd x)))

implementation Profunctor (Adapter a b) where
  dimap f g (MkApt from to) = MkApt (from . f) (g . to)

implementation Profunctor (Prism a b) where
  dimap f g (MkPrism match build) = MkPrism (mapFst g . match . f) (g . build)

implementation Profunctor (Traversal a b) where
  dimap f g (MkTrav extract) = MkTrav ((\(n' ** (v, fv)) => (n' ** (v, g . fv))) . extract . f)

parameters (p : Type -> Type -> Type)

  Optic : (a, b, s, t : Type) -> Type
  Optic a b s t = p a b -> p s t

  PrismP : (a, b, s, t : Type) -> Type
  PrismP a b s t = CoCartesian p => Optic a b s t

  LensP : (a, b, s, t : Type) -> Type
  LensP a b s t = Cartesian p => Optic a b s t

  AdapterP : (a, b, s, t : Type) -> Type
  AdapterP a b s t = Profunctor p => Optic a b s t

  TraversalP : (a, b, s, t : Type) -> Type
  TraversalP a b s t = Cartesian p => CoCartesian p => Monoidal p =>
                       Optic a b s t



--           ┌──────┐
-- (v : s) >─┤      ├─> f v
--           │      │
--       t <─┤      ├─< b
--           └──────┘
public export
record DependentLens (s, a, b : Type) (f : s -> Type) where
  constructor MkDepLens
  get : (v : s) -> f v
  set : s -> b -> t



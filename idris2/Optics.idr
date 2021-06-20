module Optics

import Data.Vect
import public Products

infixl 5 :+:
infixl 6 &&

public export
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

export
compose : Lens a b s t -> Lens s t x y -> Lens a b x y
compose (MkLens g1 s1) (MkLens g2 s2) = MkLens (\z => g1 (g2 z)) (\z => s2 (fst z, s1 (g2 (fst z), snd z)))

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

public export
interface Profunctor p where
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'

public export
interface Profunctor p => Cartesian p where
  first : p a b -> p (a :*: c) (b :*: c)
  second : p a b -> p (c :*: a) (c :*: b)

public export
interface Profunctor p => CoCartesian p where
  left : p a b -> p (a :+: c) (b :+: c)
  right : p a b -> p (c :+: a) (c :+: b)

public export
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

public export
Fn : Type -> Type -> Type
Fn a b = a -> b

public export
implementation Profunctor Fn where
  dimap f g h x = g (h (f x))

public export
implementation Cartesian Fn where
  first arg = \x => (arg (fst x), snd x)
  second arg = \x => (fst x, arg (snd x))


parameters (p : Type -> Type -> Type)

  public export
  Optic : (a, b, s, t : Type) -> Type
  Optic a b s t = p a b -> p s t

  public export
  PrismP : (a, b, s, t : Type) -> Type
  PrismP a b s t = CoCartesian p => Optic a b s t

  public export
  LensP : (a, b, s, t : Type) -> Type
  LensP a b s t = Cartesian p => Optic a b s t

  public export
  AdapterP : (a, b, s, t : Type) -> Type
  AdapterP a b s t = Profunctor p => Optic a b s t

  public export
  TraversalP : (a, b, s, t : Type) -> Type
  TraversalP a b s t = Cartesian p => CoCartesian p => Monoidal p =>
                       Optic a b s t

export
lens2Pro : Cartesian p => Lens a b s t -> Optic p a b s t
lens2Pro (MkLens get set) = (dimap (\x => (x, get x)) set) . second

export
prism2Pro : CoCartesian p => Prism a b s t -> Optic p a b s t
prism2Pro (MkPrism match build) = dimap match (either id build) . right

export
seq : Profunctor p => Optic p a b s t -> Optic p s t x y -> Optic p a b x y
seq f g z = g (f z)

stack : Profunctor p => Optic p a b s t -> Optic p q r x y -> Optic p (a,q) (b,r) (s, x) (t, y)
stack f g = ?nads

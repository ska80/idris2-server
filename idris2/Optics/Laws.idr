module Optics.Laws

import Data.Vect
import public Products

infixl 5 :+:
infixl 6 &&

funExt : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

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

export
aptToLens : Adapter a b s t -> Lens a b s t
aptToLens (MkApt from to) = MkLens from (to . snd)

public export
record Traversal (a, b, s, t : Type) where
  constructor MkTrav
  extract : s -> (n ** (Vect n a, Vect n b -> t))

public export
interface Profunctor p where
  constructor MkPro
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'
  proId : (x : p a b) -> dimap Basics.id Basics.id x = x
  proComp : {0 a, a', a'' , b, b', b'' : Type} ->
            {0 f : a'' -> a'} ->
            {0 f' : a' -> a} ->
            {0 g' : b -> b'} ->
            {0 g : b' -> b''} ->
            (x : p a b) -> dimap (f' . f) (g . g') x = dimap f g (dimap f' g' x)

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

-- A lens as a profunctor, parameterised over `a` and `b`
export
implementation Profunctor (Lens a b) where
  dimap f g (MkLens get set) = MkLens (get . f) (\x => g $ set (f (fst x), snd x))
  proId (MkLens get set) =
    cong2 MkLens
          Refl
          (funExt $ \(_,_) => Refl)
  proComp (MkLens get set) =
    cong2 MkLens
          Refl
          Refl

export
fromLens : Lens a b s t -> Profunctor (Lens a b)
fromLens x = %search

implementation Cartesian (Lens a b) where
  first (MkLens get set) = MkLens (get . fst) (\x => (set (fst (fst x), snd x), snd (fst x)))
  second (MkLens get set) = MkLens (get . snd) (\x => (fst (fst x), set (snd (fst x), snd x)))

implementation Profunctor (Adapter a b) where
  dimap f g (MkApt from to) = MkApt (from . f) (g . to)
  proId (MkApt from to) = Refl
  proComp (MkApt from to) = Refl

implementation Profunctor (Prism a b) where
  dimap f g (MkPrism match build) = MkPrism (\x => case match $ f x of Left y => Left (g y); Right y => Right y) (g . build)
  proId (MkPrism match build) = ?prismprfid
  proComp (MkPrism match build) = ?prsmPrfComp

implementation Profunctor (Traversal a b) where
  dimap f g (MkTrav extract) = MkTrav ((\(n' ** (v, fv)) => (n' ** (v, g . fv))) . extract . f)
  proId (MkTrav extract) = ?travPrfId
  proComp (MkTrav extract) = ?travPrfComp

  {-
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
{-
-}

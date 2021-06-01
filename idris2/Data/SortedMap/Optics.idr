module Data.SortedMap.Optics

import Optics
import Data.SortedMap
import Data.Either

||| Get the value at the given key
export
atIndex : SortedMap k v -> Prism v (k, v) k (SortedMap k v)
atIndex map = MkPrism (\key => maybeToEither map (lookup key map))
                      (\(key, val) => insert key val map)

export
atIndex' : CoCartesian p => SortedMap k v -> Optic p v (k, v) k (SortedMap k v)
atIndex' = prism2Pro . atIndex

fn : Profunctor p => CoCartesian p => Cartesian p => (arg -> Optic p a b s t) -> Optic p (a, arg) (b,arg) s t
fn f x = ?whut

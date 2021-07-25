module Optics.SortedMap

import Data.SortedMap
import Optics.Laws

keyLens : key -> Lens (Maybe val) val (SortedMap key val) (SortedMap key val)
keyLens key = MkLens
  (lookup key)
  (\map, newVal => insert key newVal map)

module Interfaces

import Data.Vect
import Data.SortedMap

-- Maybe I should just use elaborator reflection for that stuff

public export
interface Display (0 t : Type) where
  display : String

export
Display Bool where
  display = "Bool"

export
Display Int where
  display = "Int"

export
Display Double where
  display = "Double"

export
Display String where
  display = "String"

export
Display a => Display b => Display (Pair a b) where
  display = "(\{display {t=a}}, \{display {t=b}})"

export
Display a => Display (List a) where
  display = "List \{display {t=a}}"

export
Display Nat where
  display = "Nat"

export
Display a => Display (Vect n a) where
  display = "Vect n \{display{t=a}}"

export
Display key => Display val => Display (SortedMap key val) where
  display = "SortedMap \{display {t=key}} \{display {t=val}}"

public export
interface Default t where
  def : t

export
Default a => Default b => Default (a, b) where
  def = (def, def)

export
Default a => Default (List a) where
  def = [def, def]

export
Default Double where
  def = 0

export
Monoid t => Default t where
  def = neutral

export
Default Bool where
  def = True

public export
interface Show t => Display t => Default t => Documented t where

export
implementation Show t => Display t => Default t => Documented t where


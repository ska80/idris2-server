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
Display () where
  display = "()"

export
Display a => Display (Vect n a) where
  display = "Vect n \{display{t=a}}"

export
Display key => Display val => Display (SortedMap key val) where
  display = "SortedMap \{display {t=key}} \{display {t=val}}"

public export
interface Default t where
  def : t
  defs : List t
  defs = [def]

export
Default a => Default b => Default (Pair a b) where
  def = (def, def)
  defs = [(def1, def2) | def1 <- defs {t=a}, def2 <- defs {t=b}]

export
Default a => Default (List a) where
  def = defs {t=a} ++ defs {t=a}
  defs = [[], def]

export
Default Double where
  def = 0
  defs = [0, 3.14, -9.8]

export
Default Int where
  def = 0
  defs = [0, 1, -3]

export
Default () where
  def = ()

export
Default Bool where
  def = True
  defs = [True, False]

export
interface Show t => Display t => Default t => Documented t where

export
implementation Show t => Display t => Default t => Documented t where

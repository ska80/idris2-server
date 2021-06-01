module Server.Utils

import Data.Vect
import Data.SortedMap

infixl 3 |>

total
export
ShowType : Type -> String
ShowType String = "String"
ShowType Nat = "Nat"
ShowType Int = "Int"
ShowType Char = "Char"
ShowType (List t) = "List " ++ assert_total (ShowType t)
ShowType (Maybe t) = "Maybe " ++ assert_total (ShowType t)
ShowType (Vect _ t) = "Vect n " ++ assert_total (ShowType t)
ShowType (Pair t1 t2) = "(\{assert_total $ ShowType t1}, \{assert_total $ ShowType t2})"
ShowType (SortedMap key val) = "SortedMap \{assert_total $ ShowType key} \{assert_total $ ShowType val}"
ShowType _ = "-Unavailable-"

export
orElse : Either a b -> Either a b -> Either a b
orElse (Left x) y = y
orElse (Right x) y = Right x

export
mapElse : (err -> a) -> Either err a -> a
mapElse f = either f id

export
(|>) : (a -> b) -> (b -> c) -> a -> c
(|>) f g x = g (f x)

module Server.Utils

import Data.Vect
import Data.SortedMap

infixl 3 |>

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

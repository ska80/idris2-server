module Data.List.Optics

import Data.List
import Optics
import Products

export
matchHead : Prism a a (List a) (List a)
matchHead = MkPrism (\case [] => Left []; (x :: xs) => Right x)
                    (\x => [x])

matchTail : Prism (List a) (List a) (List a) (List a)
matchTail = MkPrism ?matchTail_rhs (\ls => ?wahu)

||| Get the list or update the first element
export
updateHead : Lens (List a) a (List a) (List a)
updateHead = MkLens id (\(xs, x) => x :: xs)

updateSecond : Cartesian p => CoCartesian p => Optic p (List a) a (List a) (List a)
updateSecond = prism2Pro matchTail . lens2Pro updateHead

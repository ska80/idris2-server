module Main

import Server
import Data.Vect
import Typedefs
import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Idris

Operations : Path
Operations = "Operation" // Cap "fst" Int // Split [
  "add" // Cap "b"           (TyTDef TNat) // Returns (Ty [] TNat) Get Ok,
  "div" // Cap "denominator" (Ty [] TNat) // Returns (Ty [] TNat) Get Ok
  ]

Range : Path
Range = "Range" // Cap "start" (TD TNat) // Cap "end" (TD TNat) // Returns (List Int) Get Ok

{-
implEx : Signature (Split [Range, Operations])
implEx = ?wait --[\a, b => [a .. b], (+), div]

main : IO ()
main = newServer (Split [Range, Operations]) implEx
-}

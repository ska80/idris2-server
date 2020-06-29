module Main

import Server
import Data.Vect
import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Idris
import Server.Typedefs


Addition : Path
Addition = "add" // TCap "a" TNat // TCap "b" TNat // TRet TNat Get Ok

addImpl : Signature Addition
addImpl = [(+)]

main : IO ()
main = newServer Addition addImpl
-- Operations : Path
-- Operations = "Operation" // Cap "fst" Nat // Split [
--   "add" // Cap "b"           Nat // Returns Nat Get Ok,
--   "div" // Cap "denominator" Nat // Returns Nat Get Ok
--   ]
--
-- Range : Path
-- Range = "Range" // Cap "start" Int // Cap "end" Int // Returns (List Int) Get Ok
--
-- implEx : Signature (Split [Range, Operations])
-- implEx = [\a, b => [a .. b], (+), divNat]
--
-- main : IO ()
-- main = newServer (Split [Range, Operations]) implEx

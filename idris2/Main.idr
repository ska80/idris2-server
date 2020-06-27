module Main

import Server

Operations : Path
Operations = "Operation" // Cap "fst" Int // Split [
  "add" // Cap "b"           Int // Returns Int Get Ok,
  "div" // Cap "denominator" Int // Returns Int Get Ok
  ]

Range : Path
Range = "Range" // Returns (List Int) Get Ok

implEx : Signature Range
implEx = ?rest
-- implEx : Signature (Split [Range, Operations])
-- implEx = ?rest

main : IO ()
main = newServer Range implEx

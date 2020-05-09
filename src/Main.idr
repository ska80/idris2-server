module Main

import Server

Operations : Path
Operations = "Operation" // Cap "fst" Int // Split [
  "add" // Cap "b"           Int // Returns Int Get Ok,
  "div" // Cap "denominator" Int // Returns Int Get Ok
  ]

Range : Path
Range = "Range" // Cap "start" Int // Cap "end" Int // Returns (List Int) Get Ok

implEx : Signature (Split [Range, Operations])
implEx = [\a, b => [a .. b], (+), div]

main : IO ()
main = newServer (Split [Range, Operations]) implEx

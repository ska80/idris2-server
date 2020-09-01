module Main

import Server

Operations : Path
Operations = "Operation" // Cap "fst" Int // Split [
  "add" // Cap "b"           Int // Returns Int Get Ok,
  "div" // Cap "denominator" Int // Returns Int Get Ok
  ]

Range : Path
Range = "Range" // Cap "lower" Nat // Cap "upper" Nat // Returns (List Nat) Get Ok

Imm : Path
Imm = Returns (List Int) Get Ok

rangeImpl : Signature Range
rangeImpl = [rangeFromTo]

immImpl : Signature Imm
immImpl = [[1,2,3]]


SplitType : Path
SplitType = "split" // Split [Range, Operations]

splitImpl : Signature (Split [Range, Operations])
splitImpl = [rangeFromTo, (+) , div]

main : IO ()
main = newServer SplitType splitImpl

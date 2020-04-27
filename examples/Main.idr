module Main

import Server


MyRoute : Path 4
MyRoute = "numerator" // Cap "num" Int // "denominator" // Cap "denom" Int // Returns Int Get Ok

MyImpl : Signature MyRoute
MyImpl num den = num `div` den

main : IO ()
main = newServer MyRoute MyImpl

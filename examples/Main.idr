module Main

import Server

MyRoute : Path
MyRoute = "numerator" // Cap "num" Int // "denominator" // Cap "denom" Int // Returns Int Get Ok

MyImpl : Signature MyRoute
MyImpl = [div]

main : IO ()
main = newServer MyRoute MyImpl

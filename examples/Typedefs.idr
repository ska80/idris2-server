module Main

import Server
import Server.Typedefs

import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Idris

MyRoute : Path
MyRoute = "numerator" // Cap "num" (TD TNat) // "denominator" // Cap "denom" (TD TNat) // Returns (TD TNat) Get Ok

MyImpl : Signature MyRoute
MyImpl = [divNat]

main : IO ()
main = newServer MyRoute MyImpl



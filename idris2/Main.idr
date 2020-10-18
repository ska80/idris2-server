module Main

import Server
import Engine

QueryOperate : Path
QueryOperate = "add" // Query ["left" :=: Int, "right" :=: Int] Int Get Ok

Range : Path
Range = "range" // Cap "low" Int // Cap "high" Int // Returns (List Int) Get Ok

implementRange : Int -> Int -> List Int
implementRange low high = [low .. high]

implementAdd : IRecord ["left" :=: Int, "right" :=: Int] -> Int
implementAdd ["left" :=: l, "right" :=: r] = l + r
implementAdd [] impossible

ServerAPI : Path
ServerAPI = Split [QueryOperate, Range]

ServerImplementation : Signature ServerAPI
ServerImplementation = [implementAdd, implementRange]

main : IO ()
main = newServer ServerAPI ServerImplementation



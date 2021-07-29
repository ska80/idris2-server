# Idris-server

Idris-server is a webserver library for Idris. It's distinctive feature is to use Idris'
first-class types in order to define your server's routes and
enforce a proper implementation of those routes. Implementing a server is as easy as:

```idris
MyRoute : Path
MyRoute = "numerator" / Cap "num" Int / "denominator" / Cap "denom" Int / Returns Int Get Ok

MyImpl : Signature () MyRoute
MyImpl = [\a, b, _ => div a b ]

main : IO ()
main = newServer MyRoute MyImpl
```

Additionally, Idris-server provides a declarative API for endpoints based on _lenses_ and lens
composition. For this import `Server.EDSL.Lenses`, here is an example:

```
InternalState : Type
InternalState = (Int, Double)

server : ServerTree InternalState
server = Prefix "path" $ Fork [ ResourceLens fstLens'
                              , ResourceLens sndLens']

main : IO ()
main = runServer Normal server (0, 3.14)
```

As you can see the server's implementation is defined using the lenses given to `ResourceLens`.
Each endpoint defined as a `ResourceLens` can be extended with the `/~` operator.

## Installation

```
> idris --install server.ipkg
```

Once the library is installed you can compile the examples by going into the examples directory
`cd examples/` and running

```
> idris -p idris-server -p contrib -o calc Calclator.idr
> ./build/exec/calc
```

This will run a mock server that read a request on stdin and print the result on stdout.

## Video presentation

https://www.youtube.com/watch?v=4xpbYPa1lTc

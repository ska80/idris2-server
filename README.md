# Idris-server

Idris-server is a webserver library for Idris. It's distinctive feature is to use Idris'
first-class types in order to defines your server's routes and its dependent types to
enforce a proper implementation of those routes. Implementing a server is as easy as:

```idris
MyRoute : Path
MyRoute = "numerator" / Cap "num" Int / "denominator" / Cap "denom" Int / Returns Int Get Ok

MyImpl : Signature () MyRoute
MyImpl = [\a, b, _ => div a b ]

main : IO ()
main = newServer MyRoute MyImpl
```

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


# Idris-server

Idris-server is a webserver library for Idris. It's distinctive feature is to use Idris'
first-class types in order to defines your server's routes and its dependent types to
enforce a proper implementation of those routes. Implementing a server is as easy as:

```idris
MyRoute : Path
MyRoute = "numerator" // Cap "num" Int // "denominator" // Cap "denom" Int // Returns Int Get Ok

MyImpl : Signature MyRoute
MyImpl = [div]

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
> idris -p server -o main Main.idr
> ./main
```

This will run a pretend server that read stdin and print the result on stdout.

## Additional features (Not yet implemented)

- Automatically derive documatation from your routes
- Automatically parses requests
- First class support for [Typedefs](https://typedefs.com)

## Why

I was bored a Friday night


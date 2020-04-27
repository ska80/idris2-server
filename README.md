
# Idris-server

Idris-server is a webserver library for Idris. It's distinctive feature is to use Idris'
first-class types in order to defines your server's routes and its dependent types to
enforce a proper implementation of those routes. Implementing a server is as easy as:

```idris
MyRoute : Path Get Ok
MyRoute = [Plain "User", Capture String, Return User]

MyImplementation : Signature MyRoute
MyImplementation name = MkUser "Martin" "Odersky"

main : IO ()
main = runServer MyRoute MyImplementation
```

## Installation

```
idris --install server.ipkg
```

Once the library is installed you can run the examples by going into the examples directory
`cd examples/` and running

```
idris -p server -p main Main.idr
```

This will run a pretend server that read stdin and print the result on stdout

## Additional features (Not yet implemented)

- Automatically derive documatation from your routes
- Automatically parses requests
- First class support for [Typedefs](https://typedefs.com)


## Why

I was bored a Friday night


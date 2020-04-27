
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

## Additional features (Not yet implemented)

- Automatically derive documatation from your routes
- Automatically parses requests
- First class support for [Typedefs](https://typedefs.com)


## Why

I was bored a Friday night


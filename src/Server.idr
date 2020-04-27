module Server

import Data.String
import Data.Vect

%access public export
%default total

data Verb = Get | Patch | Post | Put

data StatusCode : Nat -> Type where
  -- 2xx
  Ok : StatusCode 200
  Created : StatusCode 201
  Accepted : StatusCode 202
  -- 3xx
  Mutliple : StatusCode 300
  Moved : StatusCode 301

  -- 4xx
  Bad : StatusCode 400
  Unauthorized : StatusCode 401
  -- Payment : StatusCode 402
  Forbidden : StatusCode 403
  NotFound : StatusCode 404

data Response : Verb -> StatusCode n -> Type where
  MkResponse : (d : Type) -> Response v s

data Path : Nat -> Type where
  Returns : Type -> (v : Verb) -> (s : StatusCode n) -> Path Z
  Plain : String -> Path n -> Path (S n)
  Capture : (name : String) -> (t : Type)  -> Path n -> Path (S n)

infixr 5 //

interface PathComponent t where
  (//) : t -> Path n -> Path (S n)

record Capt where
  constructor Cap
  name : String
  type : Type

PathComponent String where
  (//) = Plain

PathComponent Capt where
  (//) (Cap n t) p = Capture n t p

Signature : Path n -> Type
Signature (Returns t v s) = t
Signature (Plain _ ps) = Signature ps
Signature (Capture _ t ps) = t -> Signature ps

Ret : Path n -> Type
Ret (Returns t _ _) = t
Ret (Plain _ ps) = Ret ps
Ret (Capture _ _ ps) = Ret ps

Args : Path n -> Type
Args (Returns x v s) = ()
Args (Plain x ps) = Args ps
Args (Capture name t ps) = (t, Args ps)

Parser : Type -> Type
Parser t = String -> Maybe t

interface HasParser t where
  parse : Parser t

HasParser Int where
  parse = parseInteger

HasParser String where
  parse = Just

partial
server : (path : Path n) -> Show (Ret path) =>
         (Parser (Args path)) -> ((Args path) -> (Ret path)) -> IO ()
server path parse operation = do
   str <- getLine
   let (Just args) = parse str
     | _ => do putStrLn ("fail to parse request : " ++ str); server path parse operation
   let r = operation args
   putStrLn $ "response : OK 200, body: " ++ show r
   server path parse operation

-- This combined with auto proof search is black magic to ensure we only construct paths
-- which contains types which have a `HasParser` instance. If our path contains a type
-- for which there is no `HasParser` instance the compiler with fail with "could not find
-- instance HasParser for type"
data ParsablePath : Path n -> Type where
  Nil : ParsablePath (Returns _ _ _)
  ConStr : ParsablePath ts -> ParsablePath (Plain _ ts)
  ConCap : {t : Type} -> (HasParser t) => ParsablePath ts -> ParsablePath (Capture _ t ts)

parseAll : (path : Path n) -> {auto check : ParsablePath path}
        -> Vect n String -> Maybe (Args path)
parseAll (Returns x v s) [] {check = check} = Just ()
parseAll (Plain x y) (z :: xs) {check = (ConStr w)} = if x == z then parseAll y xs else Nothing
parseAll (Capture name t x) (z :: xs) {check = (ConCap y)} = do
  [| MkPair (parse {t} z) (parseAll x xs) |]

fromSig : (path : Path n) -> Signature path -> Args path -> Ret path
fromSig (Returns x v s) fn args = fn
fromSig (Plain x y) fn args = fromSig y fn args
fromSig (Capture name t x) fn (a, b) = fromSig x (fn a) b

MkParsingFunctions : (path : Path n) -> {auto check : ParsablePath path}
                  -> String -> Maybe (Args path)
MkParsingFunctions path input {n} = do
    let splitInput = (split (== '/') input)
    correctLength <- checkLength n splitInput
    parseAll path correctLength
  where
    checkLength : (n : Nat) -> List a -> Maybe (Vect n a)
    checkLength Z [] = Just []
    checkLength Z (x :: xs) = Nothing
    checkLength (S k) [] = Nothing
    checkLength (S k) (x :: xs) = (x ::) <$>  checkLength k xs

partial
newServer : (path : Path n) -> Show (Ret path) => {auto check : ParsablePath path}
         -> (impl : Signature path) -> IO ()
newServer path impl = server path (MkParsingFunctions path) (fromSig path impl)



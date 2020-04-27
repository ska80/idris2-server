module Server

import Data.String
import Data.Vect

%access public export

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

data Path : Type where
  Returns : Type -> (v : Verb) -> (s : StatusCode n) -> Path
  Plain : String -> Path -> Path
  Capture : (name : String) -> (t : Type)  -> Path -> Path

infixr 5 //

interface PathComponent t where
  (//) : t -> Path -> Path

record Capt where
  constructor Capture'
  name : String
  type : Type

PathComponent String where
  (//) = Plain

PathComponent Capt where
  (//) (Capture' n t) p = Capture n t p

Signature : Path -> Type
Signature (Returns t v s) = t
Signature (Plain _ ps) = Signature ps
Signature (Capture _ t ps) = t -> Signature ps

Ret : Path -> Type
Ret (Returns t _ _) = t
Ret (Plain _ ps) = Ret ps
Ret (Capture _ _ ps) = Ret ps

Args : Path -> Type
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
server : (path : Path) -> Show (Ret path) =>
         (Parser (Args path)) -> ((Args path) -> (Ret path)) -> IO ()
server path parse operation = do
   str <- getLine
   let (Just args) = parse str
     | _ => do putStrLn ("fail to parse request : " ++ str); server path parse operation
   let r = operation args
   putStrLn $ "response : OK 200, body: " ++ show r
   server path parse operation

data ParsablePath : Path -> Type where
  Nil : ParsablePath (Returns _ _ _)
  ConStr : ParsablePath ts -> ParsablePath (Plain _ ts)
  ConCap : {t : Type} -> (HasParser t) => ParsablePath ts -> ParsablePath (Capture _ t ts)

parseAll : (path : Path) -> {auto check : ParsablePath path}
        -> List String -> Maybe (Args path)

fromSig : (path : Path ) -> Signature path -> Args path -> Ret path
fromSig (Returns x v s) fn args = fn
fromSig (Plain x y) fn args = fromSig y fn args
fromSig (Capture name t x) fn (a, b) = fromSig x (fn a) b

MkParsingFunctions : (path : Path ) -> {auto check : ParsablePath path}
                  -> String -> Maybe (Args path)
MkParsingFunctions path input =
  let splitInput = (split (== '/') input)
   in parseAll path splitInput


newServer : (path : Path ) -> Show (Ret path) => {auto check : ParsablePath path}
         -> (impl : Signature path) -> IO ()
newServer path impl = server path (MkParsingFunctions path) (fromSig path impl)
--

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

data PathComponent : Type where
  Plain : String -> PathComponent
  Capture : (t : Type)  -> PathComponent

MkFunction' : List PathComponent -> Response v s -> Type
MkFunction' [] (MkResponse x) = x
MkFunction' ((Plain y) :: xs) x = MkFunction' xs x
MkFunction' ((Capture t) :: xs) x = t -> MkFunction' xs x

Path : Verb -> StatusCode n -> Type
Path v s = (List PathComponent, Response v s)

MkFunction : Path v s -> Type
MkFunction = uncurry MkFunction'

interface ReturnType t where
  Returns : t -> Type

ReturnType (Response v s) where
  Returns (MkResponse t) = t

ReturnType (Path v s) where
  Returns = Returns . snd

interface Arguments t where
  Args : t -> Type

toListTypes : List PathComponent -> List Type
toListTypes [] = []
toListTypes (Plain _ :: xs) = toListTypes xs
toListTypes (Capture x :: xs) = x :: toListTypes xs

ToTuple : List Type -> Type
ToTuple [] = ()
ToTuple [x] = x
ToTuple [x, y] = (x, y)
ToTuple (x :: y :: z :: zs)= (x, ToTuple (y :: z :: zs))

Arguments (List PathComponent) where
  Args [] = ()
  Args [Plain _] = ()
  Args [Capture x] = x
  Args [Plain   _, Plain   _] = ()
  Args [Plain   _, Capture y] = y
  Args [Capture x, Plain   _] = x
  Args [Capture x, Capture y] = (x, y)
  Args (Plain   _ :: y :: z :: zs) = Args (y :: z :: zs)
  Args (Capture x :: y :: z :: zs) = (x, Args (y :: z :: zs))

Arguments (Path v s) where
  Args = Args . fst

Parser : Type -> Type
Parser t = String -> Maybe t

interface HasParser t where
  parse : Parser t

HasParser Int where
  parse = parseInteger

HasParser String where
  parse = Just

partial
server : (path : Path v s) -> Show (Returns path) =>
         (String -> Maybe (Args path)) -> ((Args path) -> (Returns path)) -> IO ()
server path parse operation = do
   str <- getLine
   let (Just args) = parse str
     | _ => do putStrLn ("fail to parse request : " ++ str); server path parse operation
   let r = operation args
   putStrLn $ "response : OK 200, body: " ++ show r
   server path parse operation

data ParsablePath : List PathComponent -> Type where
  Nil : ParsablePath []
  ConStr : ParsablePath ts -> ParsablePath (Plain _ :: ts)
  ConCap : {t : Type} -> (HasParser t) => ParsablePath ts -> ParsablePath (Capture t :: ts)

parseAll : (path : List PathComponent) -> {auto check : ParsablePath path}
        -> List String -> Maybe (Args path)
-- Nothing to parse and empty input means we're all good
parseAll [] [] {check = check} = Just ()

-- We expected nothing to parse but the input is non-empty
parseAll [] (x :: xs) {check = check} = Nothing

-- We expected at least 1 thing to parse but got no input
parseAll (_ :: _) [] {check = check} = Nothing

-- Check if the string we got is the string we expect
parseAll ((Plain x) :: []) (s :: ss) {check = check} = if x == s then Just () else Nothing

-- We expected 2 strings but got only 1
parseAll ((Plain x) :: ((Plain y) :: [])) (s :: []) {check = check} = Nothing

-- Check if the two strings we got are the ones we expect
parseAll ((Plain x) :: ((Plain y) :: [])) (s :: z :: xs) {check = check} =
  if x == s && y == z then Just () else Nothing

-- We expected at least 2 strings but got only 1
parseAll ((Plain x) :: _ :: _ :: xs) (s :: []) {check = check} = Nothing

-- we expect 2 strings but only got 1
parseAll ((Plain x) :: _ :: []) (s ::  []) {check = (ConStr y)} = Nothing

-- We expect exactly 2 strings but got more
parseAll ((Plain x) :: Capture t :: []) (s :: z :: w :: xs) {check = (ConStr y)} = Nothing

-- We expect one string and one `t` and parse them in succession
parseAll ((Plain x) :: Capture t :: []) (s :: z :: []) {check = (ConStr (ConCap y))} =
  if x == s then parse {t} z else Nothing

-- We expect at least 2 strings but got only 1
parseAll ((Plain x) :: Capture t :: (k :: xs)) (s :: []) {check = (ConStr y)} = Nothing

-- In both those clauses we expect at least 2 strings and got more to parse.
-- So we parse the first one and then recurse
parseAll (Plain x :: Plain t :: k :: xs) (s :: w :: ws) {check = (ConStr y)} =
  if x == s then parseAll (Plain t :: k :: xs) (w :: ws) else Nothing
parseAll ((Plain x) :: Capture t :: (k :: xs)) (s :: z :: ys) {check = (ConStr y)} =
  if x == s then parseAll (Capture t :: k :: xs) (z :: ys) else Nothing

-- Check if the string can be parsed into a `t`
parseAll ((Capture t) :: []) (s :: []) {check = (ConCap x)} = parse {t} s

-- We expect 1 capture but got more
parseAll ((Capture t) :: []) (s :: x :: xs) {check = check} = Nothing

-- We expect 2 strings but got only 1
parseAll ((Capture t) :: ((Plain x) :: xs)) (s :: []) {check = check} = Nothing

-- Parse the first string as a `t` and check the second string is the expected one
parseAll ((Capture t) :: ((Plain x) :: [])) (s :: (y :: [])) {check = (ConCap z)} =
  if x == y then parse {t} s else Nothing

-- We expected 2 strings and got more
parseAll [Capture t, Plain x] (s :: y :: w :: xs) {check = (ConCap z)} = Nothing

-- Parse the first string as `t` and recurse
parseAll (Capture t :: Plain x :: w :: xs) (s :: y :: ys) {check = (ConCap z)} =
  [| MkPair (parse {t} s) (parseAll (Plain x :: w :: xs) (y :: ys)) |]

-- We expected 2 captures but only got 1 string
parseAll (Capture t :: Capture x :: xs) (s :: []) {check = check} = Nothing

-- Check if the two strings parse into the two expected types from the capture
parseAll (Capture t :: Capture x :: []) (s1 :: s2 :: []) {check = ConCap (ConCap Nil)} =
  [| MkPair (parse {t} s1) (parse {t=x} s2) |]

-- We expected exactly 2 captures but got more
parseAll (Capture t :: Capture x :: []) (s1 :: s2 :: y :: xs) {check = check} = Nothing

-- Parse the first capture as `t` and recurse
parseAll (Capture t :: Capture x :: k :: ks) (s1 :: s2 :: ys) {check = ConCap z} =
  [| MkPair (parse {t} s1) (parseAll (Capture x :: k :: ks) (s2 :: ys) ) |]

MkParsingFunctions : (path : Path v s) -> {auto check : ParsablePath (fst path)}
                  -> String -> Maybe (Args path)
MkParsingFunctions (components, _) input =
  let splitInput = (split (== '/') input)
   in parseAll components splitInput

Signature : Path v s -> Type
Signature = uncurry MkFunction'

fromSig : (path : Path v s) -> Signature path -> Args path -> Returns path
fromSig ([], MkResponse t) f () = f
fromSig ((Plain s :: Plain r :: []), MkResponse t) f args = f
fromSig ((Plain s :: Plain r :: x :: xs), b) f args = fromSig (Plain r :: x :: xs, b) f args
fromSig ((Plain s :: Capture t :: []), MkResponse r) f v = f v
fromSig ((Plain s :: Capture t :: x :: xs), b) f args = fromSig ((Capture t :: x :: xs), b) f args
fromSig ((Capture t :: Plain r :: []), MkResponse u) f v = f v
fromSig ((Capture t :: Plain r :: x :: xs), MkResponse u) f (v, args) =
  fromSig (Plain r :: x :: xs, MkResponse u) (f v) args
fromSig ((Capture t :: Capture r :: []), MkResponse u) f (v, w) = f v w
fromSig ((Capture t :: Capture r :: x :: xs), b) f (v, args) =
  fromSig (Capture r :: x :: xs, b) (f v) args

newServer : (path : Path v s) -> Show (Returns path) => {auto check : ParsablePath (fst path)}
         -> (impl : Signature path) -> IO ()
newServer path impl = server path (MkParsingFunctions path) (fromSig path impl)

infix 4 +>

(+>) : List PathComponent -> Type -> Path v s
(+>) ls ret = (ls, MkResponse ret)


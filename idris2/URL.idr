
module URL

import Control.Monad.Identity
import Data.Strings
import Data.String.Parser
import Data.List1
import Data.Either
import Decidable.Equality

-------------------------------------------------------------------------
-- Non empty string proofs
-------------------------------------------------------------------------

export
data NonEmptyString : Type where
  Chars : (chars : List1 Char) -> NonEmptyString 

export
getString : NonEmptyString -> String
getString (Chars chars) = pack (forget chars)

public export
data NonEmptyProof : String -> Type where
  MkNonEmpty : (c : NonEmptyString) -> NonEmptyProof (getString c)

checkNonEmpty' : (str : List Char) -> Maybe (NonEmptyProof (pack str))
checkNonEmpty' [] = Nothing
checkNonEmpty' (x :: xs) = Just (MkNonEmpty (Chars (x ::: xs)))

unpackProof : pack (unpack str) = str
unpackProof = believe_me (Refl {x = str})

checkNonEmpty : (str : String) -> Maybe (NonEmptyProof str)
checkNonEmpty str = rewrite sym $ unpackProof {str} in checkNonEmpty' (unpack str) 

-------------------------------------------------------------------------
-- Parser Utilities
-------------------------------------------------------------------------

seq : Monad m => ParseT m a -> ParseT m b -> ParseT m (a, b)
seq a b = do va <- a
             vb <- b
             pure (va, vb)

-- pairs up two parsers seperated by a separator
pair : Monad m => ParseT m a -> (sep : ParseT m ()) -> ParseT m b -> ParseT m (a, b)
pair a sep b = do va <- a
                  skip sep
                  vb <- b
                  pure (va, vb)

nonEmptyString : Monad m => ParseT m NonEmptyString
nonEmptyString = do (c, cs) <- seq (satisfy (const True))
                                   (many (satisfy (const True)))
                    pure $ Chars (c ::: cs)

sepBy : Monad m => Char -> ParseT m a -> ParseT m (List a)
sepBy c elem = hchainl (pure <$> elem <|> pure [])
                       (char c *> pure (\acc, v => acc ++ [v]))
                       elem

pairUp : (Monad m) => ParseT m (String, String)
pairUp = do a <- takeWhile (/= '=')
            skip (char '=')
            b <- takeWhile (\x => x /= '&' && x /= '=')
            pure (a, b)

parseCompletely : ParseT Identity a -> String -> Either String a
parseCompletely p input = do (output, len) <- parse p input
                             if len /= strLength input
                                then Left "did not consume until the end"
                                else pure output

parseQuery : String -> Maybe (List (String, String))
parseQuery = eitherToMaybe . parseCompletely (sepBy '&' pairUp)

-------------------------------------------------------------------------
-- RawURL Parsing
-------------------------------------------------------------------------
  
export
record RawURL where
  constructor MkRawURL
  scheme : String
  host : String
  path : String
  queryItems :  String
  fragment : String

parseRaw : Monad m => ParseT m (RawURL)
parseRaw = [| MkRawURL parseScheme' parseHost' parsePath' parseQuery' parseFragment' |]
  where
    parseScheme' : ParseT m String
    parseScheme' = takeWhile (/= ':') <* char ':'
    parseHost' : ParseT m String
    parseHost' = (seq (char '/') (char '/')) 
              *> takeWhile (\x => x /= '/' && x /= '?' && x /= '#')
    parsePath' : ParseT m String
    parsePath' = takeWhile (\x => x /= '?' && x /= '#')
    parseQuery' : ParseT m String
    parseQuery' = takeWhile (/= '#')
    parseFragment' : ParseT m String
    parseFragment' = pack <$> many (satisfy (const True)) <* eos

||| parse a URL into it's raw form 
rawURL : String -> Maybe RawURL
rawURL x = eitherToMaybe (parseCompletely parseRaw x)

-------------------------------------------------------------------------
-- Parsing Paths
-------------------------------------------------------------------------

-- a list of '/' separated strings. Absolute paths start with '/', Relative
-- Paths start with something else
-- Examples of parsed path:
--  - "/" => Absolute ("" ::: [])
--  - "" => Relative ("" ::: [])
--  - "//" => Absolute ("" ::: [""])
--  - "a//" => Relative ("a" ::: ["", ""])
--  - "/a//" => Absolute ("a" ::: ["", ""])
--  - "/a/" => Absolute ("a" ::: [""])
--  - "a/" => Relative ("a" ::: [""])
public export
data Path : Type where
  -- Starts with /
  Absolute : List1 String -> Path
  -- Starts with no /
  Relative : List1 String -> Path

EmptyPath : Path
EmptyPath = Relative ("" ::: [])

private
parsePath' : List Char -> Path
parsePath' [] = EmptyPath
parsePath' ('/' :: xs) = Absolute (split (== '/') (pack xs))
parsePath' (x :: xs) = Relative (split (== '/') (pack (x :: xs)))

parsePath : String -> Path
parsePath = parsePath' . unpack

-------------------------------------------------------------------------
-- Verified URI type
-------------------------------------------------------------------------

public export
record Authority where
  constructor MkAuthority
  userInfo : Maybe NonEmptyString
  host : NonEmptyString
  port : Maybe NonEmptyString

-- a path from a raw string is just a path that has been split 
public export
data ParsedPath : (List1 String) -> Type where
  MkParsedPath : (path : String) -> ParsedPath (split (== '/') path)

public export
data ValidPath : (Maybe Authority) -> Path -> Type where
  NoAuthority : {a, b : String} ->
                {0 nonEmptyF : NonEmptyProof a} ->
                {0 nonEmptyS : NonEmptyProof b} ->
                ValidPath Nothing (Absolute (a ::: (b :: c)))
  HasAuthoritySlash : ValidPath (Just auth) (Absolute path)
  HasAuthorityEmpty : ValidPath (Just auth) EmptyPath

public export
data Scheme : (sch : String) -> Type where
  Empty : Scheme ""
  HTTPS : Scheme "https"
  HTTP : Scheme "http"
  FTP : Scheme "ftp"
  Mailto : Scheme "mailto"
  File : Scheme "file"
  IRC : Scheme "irc"
  Data : Scheme "data"
  Other : (s : String) -> Scheme s

MkScheme : (sch : String) -> Scheme sch
MkScheme "" = Empty
MkScheme "https" = HTTPS
MkScheme "http" = HTTP
MkScheme "ftp" = FTP
MkScheme "mailto" = Mailto
MkScheme "file" = File
MkScheme "irc" = IRC
MkScheme "data" = Data
MkScheme other = Other other

export
record URL (url : RawURL) where
  constructor MkURL
  scheme : Scheme (url.scheme)
  authority : Maybe Authority
  path : ValidPath authority (parsePath url.path)
  query : List (String, String)
  fragment : Dec (url.fragment = "")

-------------------------------------------------------------------------
-- URI Parsing Functions
-------------------------------------------------------------------------


authParser : Monad m => ParseT m Authority
authParser = [| MkAuthority (optional (nonEmptyString <* (char '@')))
                            (nonEmptyString <* ((char ':') <|> eos))
                            (optional nonEmptyString) |]

parseAuth : String -> Maybe Authority
parseAuth = eitherToMaybe . parseCompletely authParser

-- check this = Just (MkAuthority (Just "user") "host" (Just "port")
parseAuthTest1 : Maybe Authority
parseAuthTest1 = parseAuth "user@host:port"

-- check this = Just (MkAuthority Nothing "host" (Just "port")
parseAuthTest2 : Maybe Authority
parseAuthTest2 = parseAuth "host:port"

-- check this = Just (MkAuthority Nothing "host" Nothing
parseAuthTest3 : Maybe Authority
parseAuthTest3 = parseAuth "host"

-- check this = Just (MkAuthority Nothing "host" Nothing
parseAuthTest4 : Maybe Authority
parseAuthTest4 = parseAuth "@host@"

-- check this = Nothing
parseAuthTest5 : Maybe Authority
parseAuthTest5 = parseAuth "user@:port"

--  NoAuthority : {a, b : String} ->
--                {0 nonEmpty : NonEmptyProof a} ->
--                {0 nonEmpty : NonEmptyProof b} ->
--                ValidPath Nothing (Absolute (a ::: (b :: c)))
--  HasAuthoritySlash : ValidPath (Just auth) (Absolute path)
--  HasAuthorityEmpty : ValidPath (Just auth) EmptyPath
parseAuthPath : (path : Path) 
             -> (auth : Maybe Authority) 
             -> Maybe (ValidPath auth path)
parseAuthPath (Absolute (head ::: (x :: xs))) Nothing = 
  do v1 <- checkNonEmpty head
     v2 <- checkNonEmpty x
     pure $ NoAuthority {nonEmptyF = v1} {nonEmptyS = v2} 
parseAuthPath (Absolute (head ::: [])) Nothing = Nothing
parseAuthPath (Relative x) Nothing = Nothing
parseAuthPath (Absolute y) (Just x) = Just HasAuthoritySlash
parseAuthPath (Relative ("" ::: [])) (Just x) = Just HasAuthorityEmpty
parseAuthPath (Relative _) (Just x) = Nothing

||| convert an unverfied URL into a verified URL
checkURL : (url : RawURL) -> Maybe (URL url)
checkURL (MkRawURL scheme host path queryItems fragment) = do
  let auth = parseAuth host
  validPath <- parseAuthPath (parsePath path) auth
  pure $ MkURL (MkScheme scheme)
               auth
               validPath
               !(parseQuery queryItems)
               (decEq fragment "")


export
parseURL : String -> Maybe (url ** URL url)
parseURL x = do url <- rawURL x
                checked <- checkURL url
                pure (url ** checked)

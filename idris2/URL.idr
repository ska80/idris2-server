
module URL

import Data.String.ParserUtils
import Data.String.NonEmpty

import Control.Monad.Identity
import Data.Strings
import Data.List1
import Data.Either
import Decidable.Equality

-------------------------------------------------------------------------
-- RawURL Parsing
-------------------------------------------------------------------------

public export
record RawURL where
  constructor MkRawURL
  scheme : String
  host : String
  path : String
  queryItems :  String
  fragment : String

export
Show RawURL where
  show (MkRawURL scheme host path queryItems fragment) =
    "RawURL(scheme: " ++ scheme
           ++ ", host: " ++ host
           ++ ", path: " ++ path
           ++ ", queryItems: " ++ queryItems
           ++ ", fragment: " ++ fragment
           ++ ")"

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
    parseQuery' = (char '?' *> takeWhile (/= '#')) <|> pure ""
    parseFragment' : ParseT m String
    parseFragment' = (pack <$> many (satisfy (const True)) <* eos) <|> pure ""

||| parse a URL into it's raw form
rawURL : String -> Either String RawURL
rawURL = parseCompletely parseRaw

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

Eq Path where
  Absolute ls == Absolute ls' = ls == ls'
  Relative ls == Relative ls' = ls == ls'
  _ == _ = False

EmptyPath : Path
EmptyPath = Relative ("" ::: [])

export
isEmptyPath : Path -> Bool
isEmptyPath (Absolute ("" ::: [])) = True
isEmptyPath path = path == EmptyPath

private
parsePath' : List Char -> Path
parsePath' [] = EmptyPath
parsePath' ('/' :: xs) = Absolute (split (== '/') (pack xs))
parsePath' (x :: xs) = Relative (split (== '/') (pack (x :: xs)))

export
parsePath : String -> Path
parsePath = parsePath' . unpack

-------------------------------------------------------------------------
-- Verified URI type
-------------------------------------------------------------------------

||| Authority represents the middle section of a URL
||| It might represent a network path, or a DNS name or a file path, or
||| nothing.
||| UserInfo is optional and represents potential user logins for authentication
||| Host is not optional and represents the resource to reach
||| Port is optional and
public export
record Authority where
  constructor MkAuthority
  userInfo : Maybe NonEmptyString
  host : NonEmptyString
  port : Maybe NonEmptyString

Show Authority where
  show (MkAuthority userInfo host port) =
    "Authority(userInfo: " ++ show userInfo
         ++ ", host: " ++ show host
         ++ ", port: " ++ show port
         ++ ")"

public export
data ValidPath : (Maybe Authority) -> Path -> Type where
  NoAuthority : {a, b : String} ->
                {0 nonEmptyF : NonEmptyProof a} ->
                {0 nonEmptyS : NonEmptyProof b} ->
                ValidPath Nothing (Absolute (a ::: (b :: c)))
  HasAuthoritySlash : ValidPath (Just auth) (Absolute path)
  HasAuthorityEmpty : ValidPath (Just auth) EmptyPath

(path : Path) => Show (ValidPath auth path) where
  show NoAuthority {path=Absolute (a ::: (b ::c))} =
    "NoAuthority: " ++ show (a ::: (b :: c))
  show HasAuthoritySlash {path=Absolute p} =
    "HasAuthoritySlash" ++ show p
  show HasAuthorityEmpty {path=Relative ("" ::: [])} =
    "No path because of authority"

public export
data Scheme : (0 sch : String) -> Type where
  Empty : Scheme ""
  HTTPS : Scheme "https"
  HTTP : Scheme "http"
  FTP : Scheme "ftp"
  Mailto : Scheme "mailto"
  File : Scheme "file"
  IRC : Scheme "irc"
  Data : Scheme "data"
  Other : (s : String) -> Scheme s

Show (Scheme s) where
  show Empty = ""
  show HTTPS = "https"
  show HTTP = "http"
  show FTP = "ftp"
  show Mailto = "mailto"
  show File = "file"
  show IRC = "irc"
  show Data = "data"
  show (Other s) = s

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

public export
record URL (0 url : RawURL) where
  constructor MkURL
  scheme : Scheme (url.scheme)
  authority : Maybe Authority
  path : ValidPath authority (parsePath url.path)
  query : List (String, String)
  fragment : Maybe NonEmptyString


(url : RawURL) => Show (URL url) where
  show (MkURL scheme authority path query fragment) =
    "URL(scheme: " ++ show scheme
      ++ ", auth: " ++ show authority
      ++ ", path: " ++ show path
      ++ ", queryItems: " ++ show query
      ++ ", fragment: " ++ show fragment
      ++ ")"

-------------------------------------------------------------------------
-- URI Parsing Functions
-------------------------------------------------------------------------


parseQuery : String -> Maybe (List (String, String))
parseQuery = eitherToMaybe . parseCompletely (sepBy '&' pairUp)

authParser : Monad m => ParseT m Authority
authParser = [| MkAuthority (optional (nonEmptyString <* (char '@')))
                            (nonEmptyString <* ((ignore $ char ':') <|> eos))
                            (optional nonEmptyString) |]

parseAuth : String -> Maybe Authority
parseAuth = eitherToMaybe . parseCompletely authParser

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
               (checkNonEmptyString fragment)

export
parseURL : String -> Maybe (url ** URL url)
parseURL x = do url <- eitherToMaybe (rawURL x)
                checked <- checkURL url
                pure (url ** checked)



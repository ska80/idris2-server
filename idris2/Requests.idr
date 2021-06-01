module Requests

import URL
import Data.String
import Data.List1

-- data HTTPMethod = Get | Post
-- data HTTPVersion : Nat -> Nat -> Type where
--   V1991 : HTTPVersion Z 9
--   V1996 : HTTPVersion 1 0
--   V1997 : HTTPVersion 1 1
--   V2015 : HTTPVersion 2 0
--   V2020 : HTTPVersion 3 0
--
-- record Request where
--   constructor MkReq
--   method : HTTPMethod
--   version : (min ** maj ** HTTPVersion min maj)
--   headers : List String
--   path : List String
--   body : String

public export
parseRequest : String -> Maybe (List String, Maybe String)
parseRequest str =
  case words str of
       ["GET", path] => Just (forget $ split (=='/') path, Nothing)
       ["POST", path, body] => Just (forget $ split (=='/') path, Just body)
       _ => Nothing



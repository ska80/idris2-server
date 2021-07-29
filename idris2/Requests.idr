module Requests

import URL
import Data.String
import Data.List1
import Data.List

public export
data HTTPMethod = Get | Post

export
Show HTTPMethod where
  show Get = "GET"
  show Post = "POST"

export
Eq HTTPMethod where
  Get == Get = True
  Post == Post = True
  _ == _ = False

export
data HTTPVersion : Nat -> Nat -> Type where
  V1991 : HTTPVersion Z 9
  V1996 : HTTPVersion 1 0
  V1997 : HTTPVersion 1 1
  V2015 : HTTPVersion 2 0
  V2020 : HTTPVersion 3 0

public export
record Request where
  constructor MkReq
  method : HTTPMethod
  version : (min ** maj ** HTTPVersion min maj)
  headers : List (String, String)
  path : List String
  body : String

export
Show Request where
  show (MkReq meth (n ** m ** ver) heads path body) = """
      \{show meth} \{concat (intersperse "/" path)} \{showVersion}
      \{concat $ intersperse "\n" $ map (\(hd, con) => "\{hd}: \{con}") heads}
      \{body}
      """
      where
        showVersion : String
        showVersion = "HTTP/\{show n}.\{show m}"

public export
parseRequest : String -> Maybe Request
parseRequest str =
  case words str of
       ["GET", path] => Just $
                       MkReq Get
                       (2 ** 0 ** V2015)
                       [("User-Agent", "Idris/0.4")
                       ,("Host", "localhost")]
                       (forget $ split (=='/') path)
                       ""
       ["POST", path, body] => Just $
                       MkReq Post
                       (2 ** 0 ** V2015)
                       [("User-Agent", "Idris/0.4")
                       ,("Host", "localhost")]
                       (forget $ split (=='/') path)
                       body
       _ => Nothing



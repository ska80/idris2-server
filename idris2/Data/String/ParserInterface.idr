module Data.String.ParserInterface

import Data.Strings

------------------------------------------------------------------------
-- Parser Interface
------------------------------------------------------------------------

public export
Parser : Type -> Type
Parser a = String -> Maybe a

public export
interface HasParser t where
  parse : Parser t

export
HasParser Nat where
  parse = map fromInteger . parseInteger

export
HasParser Int where
  parse = parseInteger

export
HasParser String where
  parse = Just

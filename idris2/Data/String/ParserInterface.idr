module Data.String.ParserInterface

import Data.Strings
import Data.SortedMap

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

export
HasParser () where
  parse "" = Just ()
  parse _ = Nothing

export
implementation HasParser a => HasParser (List a) where
  parse "[]" = Just []
  parse str = Nothing

export
implementation HasParser key => HasParser val => HasParser (SortedMap key val) where
  parse _ = Nothing

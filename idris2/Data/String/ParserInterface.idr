module Data.String.ParserInterface

import Data.SortedMap
import Data.String
import Data.String.Parser

------------------------------------------------------------------------
-- Parser Interface
------------------------------------------------------------------------

removeCommonPrefix : (pre, input : String) -> Maybe String
removeCommonPrefix pre input =
  let pre' = unpack pre
      inp = unpack input in
      checkPrefix pre' inp
      where checkPrefix : List Char -> List Char -> Maybe String
            checkPrefix [] rest = Just $ pack rest --all good
            checkPrefix (x :: xs) [] = Nothing -- prefix longer
            checkPrefix (x :: xs) (y :: ys) = if x == y -- keep going if same
                                                 then checkPrefix xs ys
                                                 else Nothing

public export
interface HasParser t where
  partialParse : Parser t

export
parse : (HasParser t) => String -> Maybe t
parse input = case parse (partialParse <* eos) input of
                   Left _ => Nothing
                   Right (v, _) => Just v

export
HasParser Bool where
  partialParse = string "true" *> pure True <|> string "false" *> pure False

export
HasParser Nat where
  partialParse = natural

export
HasParser Int where
  partialParse = cast <$> integer

export
HasParser Double where
  partialParse =  do
      let minus : Double = if !(succeeds (char '-')) then (-1) else 1
      leading <- option ['0'] (some (satisfy isDigit))
      ignore $ char '.'
      mantissa <- some (satisfy isDigit)
      let double = "\{pack leading}.\{pack mantissa}"
      case parseDouble double of
           Nothing => fail "expected Double, got \{double} instead"
           Just d => pure (minus * d)


export
HasParser String where
  -- we assume strings are just the whole (nonempty) input
  partialParse = takeWhile1 (const True)

export
HasParser () where
  partialParse = pure ()

export
implementation HasParser a => HasParser b => HasParser (a, b) where
  partialParse = do
    ignore $ char '('
    v1 <- partialParse {t=a}
    ignore $ char ','
    v2 <- partialParse {t=b}
    ignore $ char ')'
    pure (v1, v2)

export
implementation HasParser a => HasParser (List a) where
  partialParse = do
    ignore $ char '['
    hchainr (partialParse {t=a}) (char ',' *> pure (::)) (char ']' *> pure Nil)

-- sorted maps are parsed from lists of pairs
export
implementation Ord key => HasParser key => HasParser val => HasParser (SortedMap key val) where
  partialParse = fromList <$> partialParse

  {-
  -}

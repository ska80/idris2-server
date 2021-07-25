module Data.String.ParserUtils

import Data.Either
import Data.String.NonEmpty
import Data.String
import Data.List1
import public Control.Monad.Identity
import public Data.String.Parser

-------------------------------------------------------------------------
-- Parser Utilities
-------------------------------------------------------------------------

export
seq : Monad m => ParseT m a -> ParseT m b -> ParseT m (a, b)
seq a b = do va <- a
             vb <- b
             pure (va, vb)

-- pairs up two parsers seperated by a separator
export
pair : Monad m => ParseT m a -> (sep : ParseT m ()) -> ParseT m b -> ParseT m (a, b)
pair a sep b = do va <- a
                  skip sep
                  vb <- b
                  pure (va, vb)

export
nonEmptyString : Monad m => ParseT m NonEmptyString
nonEmptyString = do (c, cs) <- seq (satisfy (const True))
                                   (many (satisfy (const True)))
                    pure $ Chars (c ::: cs)

export
sepBy : Monad m => Char -> ParseT m a -> ParseT m (List a)
sepBy c elem = hchainl (pure <$> elem <|> pure [])
                       (char c *> pure (\acc, v => acc ++ [v]))
                       elem

export
pairUp : (Monad m) => ParseT m (String, String)
pairUp = pair (takeWhile (/= '='))
              (skip (char '='))
              (takeWhile (\x => x /= '&' && x /= '='))

export
parseCompletely : ParseT Identity a -> String -> Either String a
parseCompletely p input = do (output, len) <- parse p input
                             if len /= strLength input
                                then Left "Did not consume until the end."
                                else pure output


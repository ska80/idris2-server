module Data.String.NonEmpty

import Data.List1

-------------------------------------------------------------------------
-- Non empty string proofs
-------------------------------------------------------------------------

public export
data NonEmptyString : Type where
  Chars : (chars : List1 Char) -> NonEmptyString

public export
Show NonEmptyString where
  show (Chars chars) = pack (forget chars)

export
getString : NonEmptyString -> String
getString (Chars chars) = pack (forget chars)

public export
data NonEmptyProof : String -> Type where
  MkNonEmpty : (c : NonEmptyString) -> NonEmptyProof (getString c)

toNonEmptyString : NonEmptyProof str -> NonEmptyString
toNonEmptyString (MkNonEmpty c) = c

checkNonEmpty' : (str : List Char) -> Maybe (NonEmptyProof (pack str))
checkNonEmpty' [] = Nothing
checkNonEmpty' (x :: xs) = Just (MkNonEmpty (Chars (x ::: xs)))

private
unpackProof : pack (unpack str) = str
unpackProof = believe_me (Refl {x = str})

export
checkNonEmpty : (str : String) -> Maybe (NonEmptyProof str)
checkNonEmpty str = rewrite sym $ unpackProof {str} in checkNonEmpty' (unpack str)

export
checkNonEmptyString : String -> Maybe (NonEmptyString)
checkNonEmptyString str = map toNonEmptyString (checkNonEmpty str)


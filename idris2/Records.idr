module Records

import Data.String.ParserInterface

%default total

infixl 9 :=:

||| Description of a record row with key and type
public export
data Row : String -> Type -> Type where
  (:=:) : (s : String) -> (t : Type) -> HasParser t => Row s t

public export
data Record : Type where
  Nil : Record
  (::) : (Row key type) -> Record -> Record



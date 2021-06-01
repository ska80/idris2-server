module Records

import Data.String.ParserInterface
import Server.Utils

%default total

infixl 9 :=:


||| Description of a record row with key and type
public export
data Row : String -> Type -> Type where
  (:=:) : (s : String) -> (t : Type) -> HasParser t => Row s t

export
Show (Row r t) where
  show (s :=: t) = "\{s} :=: \{assert_total $ ShowType t}"

public export
data Record : Type where
  Nil : Record
  (::) : (Row key type) -> Record -> Record

printList : Record -> List String
printList [] = []
printList (x :: y) = show x :: printList y

export
Show Record where
  show rec = show (printList rec)

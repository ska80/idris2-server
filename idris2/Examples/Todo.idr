module Examples.Todo

import Server
import Engine
import EDSL
import Optics
import Data.List
import Data.List.Optics
import Data.SortedMap
import Data.SortedMap.Optics
import Data.Vect

import Prelude as P

%hide Prelude.(/)

infixr 5 /

updateList : CoCartesian p => Cartesian p =>
             k -> SortedMap k (List v) ->
             Optic p (List v) v k (SortedMap k (List v))
updateList key map =
  let mIndxed = atIndex' {p} map
      lsHead = lens2Pro {p} (updateHead {a=v})
   in mIndxed . dimap id (key,) . lsHead

update : Monoid v => k -> (v -> v) -> SortedMap k v -> SortedMap k v
update k f m =
  let v = fromMaybe neutral $ lookup k m in
    insert k (f v) m

Todo : Type
Todo = String

getTodo : Path
getTodo = "todo" / Cap "user" Int / Returns (List Todo) Get

setTodo : Path
setTodo = "todo" / Cap "User" Int / Returns (List Todo) (Post Todo)

TodoAPI : Path
TodoAPI = Split [getTodo, setTodo]

TodoResource : Path
TodoResource = "todo" / Cap "User" Int / Resource Todo (List Todo)

ServerState : Type
ServerState = SortedMap Int (List Todo)

initial : ServerState
initial = empty

todoImpl : Signature ServerState TodoAPI
todoImpl = [findTodo, updateTodo]
  where
    findTodo : Int -> ServerState -> List Todo
    findTodo id state = fromMaybe [] (lookup id state)

    updateTodo : Int -> Todo -> ServerState -> (List Todo, ServerState)
    updateTodo id todo state = (todo :: findTodo id state, update id (todo ::) state)

main : IO ()
main = Engine.newServer empty TodoResource todoImpl

{-
-}

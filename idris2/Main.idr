module Main

import Server
import Engine
import Control.Monad.Converter
import Control.Monad.State
import Data.IORef
import Data.Nat

%ambiguity_depth 4

-- QueryOperate : Path IO
-- QueryOperate = "add" // Query ["left" :=: Int, "right" :=: Int] Int Get Ok
--
-- Range : Path IO
-- Range = "range" // Cap "low" Int // Cap "high" Int // Returns (List Int) Get Ok
--
-- implementRange : Int -> Int -> IO (List Int)
-- implementRange low high = pure $ [low .. high]
--
-- implementAdd : IRecord ["left" :=: Int, "right" :=: Int] -> IO Int
-- implementAdd ["left" :=: l, "right" :=: r] = pure $ l + r
-- implementAdd [] impossible
--
-- ServerAPI : Path IO
-- ServerAPI = Split [QueryOperate, Range]
--
-- ServerImplementation : Signature IO ServerAPI
-- ServerImplementation = [implementAdd, implementRange]
--
-- main : IO ()
-- main = newServer Range [implementRange]

findAndUpdate : (a -> a) -> (a -> Bool) -> List a -> List a
findAndUpdate = update []
  where
    update : List a -> (a -> a) -> (a -> Bool) -> List a -> List a
    update acc f p [] = reverse acc
    update acc f p (x :: xs) = if p x then (reverse acc) ++ f x :: xs
                                      else update (x :: acc) f p xs

record Item where
  constructor MkItem
  id : Int
  content : String
  completed : Bool

Show Item where
  show (MkItem id body completed) =
    "Item " ++ show id ++ " " ++ show body ++ if completed then " done"
                                                           else " to do"

-- The state of the server is a pair with the list of tasks and an increasing
-- id number
ServerState : Type
ServerState = (List Item, Nat)

-- GET / => Render the list
-- POST /items => Creat new item
-- POST /items/:id/done => Complete item
-- POST /items/:id/delete => Delete item
todoAPI : Path
todoAPI = Split [ Returns (List Item) Get Ok
                , "items" // Returns Item Post Ok
                , "items" // Cap "id" Int // "done" // Returns () Post Ok
                , "items" // Cap "id" Int // "delete" // Returns () Post Ok
                ]
-- Returning the list of items amounts to returning the first element of the
-- global state
retList : State ServerState (List Item)
retList = map fst get

-- Completing an Item changes the global state. The changes amounts to finding
-- the item and then updating it to set its "completed" field to 'True'
completeItem : Int -> State ServerState ()
completeItem itemId = modify (mapFst updateList)
  where
    updateList : List Item -> List Item
    updateList = findAndUpdate
                     (record {completed = True}) -- set the task to completed
                     ((itemId ==) . id)          -- if the id matches

-- Deleting an item amounts to changing the global state by filtering items
-- which have the given `id`
deleteItem : Int -> State ServerState ()
deleteItem itemId = modify $ -- update the state
                    mapFst $ -- only update the list of items
                    filter ((== itemId) . id) --filter the list

-- Creating an item makes use of the counter in the global state to create
-- a new ID
createItem : State ServerState Item
createItem = do
  (items, n) <- get -- get the state
  let newItem = MkItem (cast $ S n) "" False -- make a new item
  modify $ bimap (newItem ::) S -- add the item to the list, increment the count
  pure (id newItem) -- return the new item's id

-- To implement our server we need to provide the 4 functions described by
-- the APi
todoImpl : Signature (State ServerState) Main.todoAPI
todoImpl = [retList , createItem, completeItem, deleteItem]

-- In order to run the server we need to supply it with an initial state
-- which will be stored as an IORef
main : IO ()
main = do ref <- newIORef ([], Z)
          newServer todoAPI todoImpl


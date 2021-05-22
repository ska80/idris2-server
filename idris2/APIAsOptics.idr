module APIAsOptics

import Server
import Optics
import Control.Monad.Identity

data Status = Done | NotDone

Show Status where
  show Done = "Done"
  show NotDone = "NotDone"

record Todo where
  constructor MkTodo
  id : Int
  content : String
  status : Status

Show Todo where
  show (MkTodo id c s) = "Todo(id: \{show id}, content: \{c}, status: \{show s})"

api : PathComp 2
api = Str "todo" $ Tpe String $ End Nothing (List Todo)
-- api = "todo" // Cap "user" String // Returns (List Todo) Get Ok

pathToOptic : Profunctor p => Cartesian p => CoCartesian p => Monoidal p =>
              (path : PathComp n) -> (impl : PathToArgs path) -> Optic p (Ret path) (Args path) (Args path) (Ret path)
pathToOptic path impl = dimap impl impl

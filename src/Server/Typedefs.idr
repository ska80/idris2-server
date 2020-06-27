module Typedefs

import Data.Vect
import Server
import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Idris
import Typedefs.TermParse
import Typedefs.TermWrite
import Language.JSON

public export
data TD : TDefR 0 -> Type where
  MkTy : (t : Ty' StandardIdris [] td) -> TD td

public export
Server.HasParser (TD td) where
  parse input {td} = do
    json <- JSON.parse input
    parsed <- eitherToMaybe $ deserialise {format=JSON}
                StandardParsers
                []
                td
                json
    pure $ MkTy parsed

public export
Show (TD td) where
  show (MkTy val) {td} = show $ serialise {target=JSON} StandardContext [] td val

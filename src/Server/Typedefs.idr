module Typedefs

import Data.Vect
import Server
import Typedefs.Typedefs
import Typedefs.Library
import Typedefs.Idris
import Typedefs.TermParse
import Typedefs.TermWrite
import Language.JSON

-- public export
-- data TD : TDefR 0 -> Type where
--   MkTy : (t : Ty' StandardIdris [] td) -> TD td
--

public export
tdefParser : (td : TDefR 0) -> Server.HasParser (Ty' StandardIdris [] td)
tdefParser td = MkParse $ \input => do
    json <- JSON.parse input
    eitherToMaybe $ deserialise {format=JSON}
        StandardParsers
        []
        td
        json


tdefDisplay : (td : TDefR 0) -> DisplayFn (Ty' StandardIdris [] td)
tdefDisplay td = Display $ \val => show $ serialise {target=JSON} StandardContext [] td val

export
TRet : TDefR 0 -> Verb -> StatusCode n -> Path
TRet tdef v s = Returns (Ty' StandardIdris [] tdef) v s {display = (tdefDisplay tdef)}

public export
data TCapt : Type where
  TCap : (name : String) -> TDefR 0 -> TCapt

public export
PathBuilder TCapt where
  (//) (TCap n tdef) ps = Capture n (Ty' StandardIdris [] tdef) {parser = tdefParser tdef} ps

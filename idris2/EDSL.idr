module EDSL

import Server


infixr 5 /

public export
data Capt : Type where
  Cap : (name : String) -> (t : Type) -> HasParser t => Capt

public export
interface PathBuilder t where
  (/) : t -> Path -> Path

public export
PathBuilder String where
  (/) = Plain

public export
PathBuilder Capt where
  (/) (Cap n t) p = Capture n t p

namespace EDSL
  public export
  Query :  Record -> (t : Type) -> Show t =>
         (v : Verb) -> Path
  Query rec t v = Ends (Just rec) t v

  public export
  Returns : (t : Type) -> Show t =>
          (v : Verb) -> Path
  Returns t v = Ends Nothing t v

  public export
  Resource : (val : Type) -> (ret : Type) -> Show ret => HasParser val => Path
  Resource val ret = Split [Ends Nothing ret Get,
                            Ends Nothing ret (Post val)
                           ]


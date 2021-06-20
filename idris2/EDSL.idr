module EDSL

import Server
import Optics

%ambiguity_depth 5

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

  public export
  Lens : {a, b : Type} -> Lens a a b (a, b) -> HasParser b => Show a => Path
  Lens opt = Split [ Returns a Get, Returns a (Post b) ]

infixr 5 ~/

(~/) : Path -> Path -> Path
(~/) (Ends queryItems returnType v) y = y
(~/) (Plain x ps) y = Plain x (ps ~/ y)
(~/) (Capture name t ps) y = Capture name t (ps ~/ y)
(~/) (Split xs) y = Split (map ( ~/ y) xs)

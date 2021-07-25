module Server.Documentation

import Server
import Data.Maybe
import public Text.PrettyPrint.PrettyPrinter

data ReqType = GetReq | PostReq

Show ReqType where
  show GetReq = "GET"
  show PostReq = "POST"

record DisplayEndpoint where
  constructor MkDisplay
  arguments : List (Either String (t : Type ** Documented t))
  queryParam : Maybe Record
  requestType : ReqType
  returnType : (t : Type ** Documented t)

intersperse : Doc ann -> List (Doc ann) -> Doc ann
intersperse = encloseSep neutral neutral

renderEndpoint : Maybe (Doc String) -> DisplayEndpoint -> Doc String
renderEndpoint desc (MkDisplay args qry req (ret ** _)) =
  vsep
  [ pretty (show req) <++> intersperse (pretty "/") (map typeToDoc args)
  , pretty "returns:" <++> pretty (display {t=ret})
  , pretty "query parameters:" <++> maybe (pretty "none") (pretty . show) qry
  , pretty "example:" <++> renderExample
  , pretty "description:" <++> fromMaybe (pretty "none") desc
  ]
  where
    ||| Generate a description of the given type
    typeToDoc : Either String (t ** Documented t) -> Doc String
    typeToDoc (Left str) = pretty str
    typeToDoc (Right (t ** _)) = pretty (display {t})

    ||| generate a default value for the given type
    typeToDefault : Either String (t : Type ** Documented t) -> Doc String
    typeToDefault (Left str) = pretty str
    typeToDefault (Right (t ** _)) = pretty (show (def {t}))

    renderExample : Doc String
    renderExample = intersperse (pretty "/") (map typeToDefault args)

||| Given a path component and an optional description, generate the documentation
||| corresponding to the endpoint
export
generateDoc : {n : Nat} -> PathComp n st -> Maybe (Doc String) -> Doc String
generateDoc path desc = renderEndpoint desc (generateAcc _ path [])
  where
    generateAcc : (0 n : Nat) -> PathComp n st -> List (Either String (t ** Documented t)) -> DisplayEndpoint
    generateAcc _ (End Nothing (Query _) ret) args =
      MkDisplay (reverse args) Nothing GetReq (ret ** %search)
    generateAcc _ (End Nothing (Update v _) ret) args =
      MkDisplay (reverse args) Nothing PostReq (ret ** %search)
    generateAcc _ (End (Just q) (Query _) ret) args =
      MkDisplay (reverse args) (Just q) GetReq (ret ** %search)
    generateAcc _ (End (Just q) (Update v _) ret) args =
      MkDisplay (reverse args) (Just q) PostReq (ret ** %search)
    generateAcc _ (Str x y) args =
      generateAcc _ y (Left x :: args)
    generateAcc _ (Tpe t x) args =
      generateAcc _ x (Right (t ** %search):: args)

vvsep : List (Doc a) -> Doc a
vvsep = concatWith (\x, y => x <+> line <+> line <+> y)

export
generateDocs : List ((n ** PathComp n st), Maybe (Doc String)) -> Doc String
generateDocs = vvsep . map (\case ((_ ** path), desc) => generateDoc path desc)

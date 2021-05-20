module Products

infixl 6 :*:

public export
(:*:) : Type -> Type -> Type
(:*:) = Pair

export
fork : (a -> b) -> (a -> c) -> a -> (b, c)
fork f g x = (f x, g x)


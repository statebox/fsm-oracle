module Utils.Either

export
mapLeft : (a -> b) -> Either a c -> Either b c
mapLeft f (Left a) = Left (f a)
mapLeft _ (Right v) = Right v


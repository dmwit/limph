arg1 :: m a
arg2 :: m b
func :: a -> b -> m c

foo :: m c
foo = func arg1 arg2

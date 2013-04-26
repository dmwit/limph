
foo :: Bool -> MaybeT [] a
foo x = if x then [] else Nothing
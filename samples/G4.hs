
foo :: Bool -> ListT Maybe a
foo x = if x then [] else Nothing
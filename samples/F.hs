{-# LANGUAGE LIMPH #-}
import Common

foreign import negfunc :: IO a -> IO b

foo :: IO a
foo = negfunc ()

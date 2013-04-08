{-# LANGUAGE LIMPH #-}
import Common

foo :: MaybeT IO a
foo = funcMixedArguments maybe io

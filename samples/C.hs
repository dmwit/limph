{-# LANGUAGE LIMPH #-}
import Common

foo :: MaybeT IO a
foo = maybetio >> maybe

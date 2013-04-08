{-# LANGUAGE LIMPH #-}
import Common

foo :: MaybeT IO a
foo = do
	maybetio
	io

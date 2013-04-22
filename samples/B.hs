{-# LANGUAGE LIMPH #-}
import Common

foreign import maybetio :: MaybeT IO a
foreign import io       ::        IO a

foo :: MaybeT IO a
foo = do
	maybetio
	io

{-# LANGUAGE LIMPH #-}
import Common

foreign import func  :: a -> b -> MaybeT IO c
foreign import maybe :: Maybe a
foreign import io    :: IO    a

foo :: MaybeT IO a
foo = func maybe io

-- desired result: foo = liftM2 func (liftMaybeToMaybeTIO maybe) (liftIOToMaybeTIO io)

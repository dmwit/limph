{-# LANGUAGE LIMPH #-}
import Common

foreign import func  :: a -> b -> MaybeT IO c
foreign import maybe :: Bot (Maybe a)
foreign import io    :: IO a

foo = func maybe io

-- desired result: foo = liftM (func maybe) (liftIOToMaybeTIO io)

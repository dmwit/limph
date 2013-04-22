
{-# LANGUAGE LIMPH #-}
import Common

foreign import func  :: a -> b -> MaybeT IO c
foreign import maybe :: Bot (Maybe a)
foreign import io    :: IO a

foo = func (join maybe) io

-- desired result: foo = liftM2 func (liftMaybeToMaybeTIO (join (liftBotToMaybe maybe))) (liftIOToMaybeTIO io)

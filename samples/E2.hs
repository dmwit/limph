{-# LANGUAGE LIMPH #-}
import Common

foreign import func  :: a -> Bot (b -> MaybeT IO c)
foreign import maybe :: Bot (Maybe a)
foreign import io    :: IO a

foo = func maybe io

-- desired result (?):
-- foo = do
--     a <- liftBotToMaybeTIO maybe
--     f <- liftBotToMaybeTIO (func a)
--     b <- liftIOToMaybeTIO  io
--     f b

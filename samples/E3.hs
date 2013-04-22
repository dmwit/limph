{-# LANGUAGE LIMPH #-}
import Common

foreign import func  :: a -> Bot (b -> MaybeT IO c)
foreign import maybe :: Bot (Maybe a)
foreign import io    :: IO a

foo = func (join maybe) io

-- desired result (?):
-- foo = do
--     a <- liftMaybeToMaybeTIO $ do
--        tmp <- liftBotToMaybe maybe
--        join tmp
--     f <- liftBotToMaybeTIO (func a)
--     b <- liftIOToMaybeTIO io
--     f b

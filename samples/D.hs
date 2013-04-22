{-# LANGUAGE LIMPH #-}
import Common

foreign import maybetio :: MaybeT IO a
foreign import maybe    :: Maybe     a
foreign import monadio  :: MonadIO m => m a

foo :: MaybeT IO a
foo = maybetio >> maybe >> monadio

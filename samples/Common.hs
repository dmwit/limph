-- no extension used in this file, to avoid issues with undefined for now
module Common
	( module Common
	, module Control.Monad.Trans.Maybe
	) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe

io :: IO a
io = undefined

maybe :: Maybe a
maybe = undefined

maybetio :: MaybeT IO a
maybetio = undefined

monadio :: MonadIO m => m a
monadio = undefined

func :: a -> b -> MaybeT IO c
func = undefined

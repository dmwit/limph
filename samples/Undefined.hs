import           Control.Monad.Reader
import           Control.Monad.Trans

-- We have to use a data type because otherwise we can't distinguish
-- _|_ and IdentityT _|_ by definition.
data IdentityT m a = IdentityT { runIdentityT :: m a }

instance (Functor m) => Functor (IdentityT m) where
    fmap f = mapIdentityT (fmap f)

-- Note the funny implementation of >>= which is unnecessarily strict
-- in its first argument.  I'm pretty sure this is still valid, but
-- most monad transformers have an implementation of >>= which is
-- nonstrict in its first argument, in which case (I'm pretty sure) it
-- is impossible to distinguish _|_ from lift _|_.
instance (Monad m) => Monad (IdentityT m) where
    return = IdentityT . return
    (IdentityT m) >>= k = IdentityT $ runIdentityT . k =<< m

instance MonadTrans IdentityT where
    lift = IdentityT

mapIdentityT :: (m a -> n b) -> IdentityT m a -> IdentityT n b
mapIdentityT f = IdentityT . f . runIdentityT

-- We have to use a monad whose >>= is non-strict in its first
-- argument, here Reader.  e.g. replacing Reader with Maybe does not
-- work -- context a and context b are both _|_ in that case.

a :: IdentityT (Reader e) a
a = undefined

b :: IdentityT (Reader e) a
b = lift undefined

context :: IdentityT (Reader ()) a -> Int
context m = runReader (runIdentityT (m >> return 3)) ()

-- Try evaluating context a  and  context b!

{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}

module TCPropVar where

import           Control.Applicative
import           Control.Monad.Error
import           Control.Monad.Logic
import           Control.Monad.State
import           Control.Monad.Supply
import           Control.Unification hiding (unify)
import           Control.Unification.IntVar
import           Data.Default
import           Data.Foldable
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Traversable

type Var  = String
type PVar = Var
type Name = String

data Term
  = Lambda Var Term
  | TermVar Var
  | Term :@ Term
  deriving (Eq, Ord, Show, Read)

data Type p v
  = TypeVar v
  | TConst Name
  | PApp p (Type p v) (Type p v)
  | TApp (Type p v) (Type p v)
  | Type p v :-> Type p v
  deriving (Eq, Ord, Show, Read)

data Constraint
  = T
  | F
  | CVar PVar
  | Neg Constraint
  | Constraint :\/: Constraint
  | Constraint :/\: Constraint
  | Var :==: Type () Var
  deriving (Eq, Ord, Show, Read)

  -- XXX do we also need morphism constraints?

-- some smart constructors

neg :: Applicative f => Constraint -> f Constraint
neg T       = pure F
neg F       = pure T
neg (Neg c) = pure c
neg c       = pure $ Neg c

infixr 2 \/
infixr 3 /\

(\/) :: Applicative f => f Constraint -> f Constraint -> f Constraint
(\/) = liftA2 orOpt

orOpt :: Constraint -> Constraint -> Constraint
orOpt T  _  = T
orOpt F  c  = c
orOpt _  T  = T
orOpt c  F  = c
orOpt c1 c2 = c1 :\/: c2

(/\) :: Applicative f => f Constraint -> f Constraint -> f Constraint
(/\) = liftA2 andOpt

andOpt :: Constraint -> Constraint -> Constraint
andOpt T  c  = c
andOpt F  _  = F
andOpt c  T  = c
andOpt _  F  = F
andOpt c1 c2 = c1 :/\: c2

type M a = Supply Var a

fresh :: Supply Var Var
fresh = supply

unify :: Type PVar Var -> Type PVar Var -> M Constraint
unify (TConst k1) (TConst k2) | k1 == k2 = pure T
unify (PApp p s1 s2) t = (pure (CVar p) /\ unify (TApp s1 s2) t) \/
                         (neg  (CVar p) /\ unify          s2  t)
unify s (PApp p t1 t2) = (pure (CVar p) /\ unify s (TApp t1 t2)) \/
                         (neg  (CVar p) /\ unify s          t2)
unify (TApp s1 s2) (TApp t1 t2) = unify s1 t1 /\ unify s2 t2
unify (TypeVar a)  t@(TApp {}) = do
  a1 <- fresh
  a2 <- fresh
  let a' = TApp (TypeVar a1) (TypeVar a2)
  pure (a :==: a') /\ unify a' t
unify t@(TApp {}) (TypeVar a) = do
  a1 <- fresh
  a2 <- fresh
  let a' = TApp (TypeVar a1) (TypeVar a2)
  pure (a :==: a') /\ unify t a'
unify (s1 :-> s2) (t1 :-> t2) = unify s1 t1 /\ unify s2 t2
unify (TypeVar a) t@(_ :-> _) = do
  a1 <- fresh
  a2 <- fresh
  let a' = TypeVar a1 :-> TypeVar a2
  pure (a :==: a') /\ unify a' t
unify t@(_ :-> _) (TypeVar a) = do
  a1 <- fresh
  a2 <- fresh
  let a' = TypeVar a1 :-> TypeVar a2
  pure (a :==: a') /\ unify t a'
unify (TypeVar a) (TConst k)  = pure (a :==: TConst k)
unify (TConst k)  (TypeVar a) = pure (a :==: TConst k)
unify (TypeVar a) (TypeVar b) = pure (a :==: TypeVar b)

-- Remaining cases are all two different constructors among TConst,
-- TApp, :->, or two TConst that do not match
unify _ _ = pure F


ty1, ty2 :: Type PVar Var
-- (a -> a) -> a
ty1 = (TypeVar "a" :-> TypeVar "a") :-> TypeVar "a"

-- m_p (b -> m_q c)
ty2 = PApp "p" (TypeVar "m") (TypeVar "b" :-> PApp "q" (TypeVar "m") (TypeVar "c"))

{-
>>> evalSupply (unify ty1 ty2) (map show [0..])
Neg (CVar "p") :/\: ((("b" :==: (TypeVar "0" :-> TypeVar "1")) :/\: (("a" :==: TypeVar "0") :/\: ("a" :==: TypeVar "1"))) :/\: ((CVar "q" :/\: (("a" :==: TApp (TypeVar "2") (TypeVar "3")) :/\: (("2" :==: TypeVar "m") :/\: ("3" :==: TypeVar "c")))) :\/: (Neg (CVar "q") :/\: ("a" :==: TypeVar "c"))))
-}

data TypeF v
  = TConstF Name
  | TAppF v v
  | v :->: v
  deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

-- actually not going to use this instance, but it's required by
-- unification-fd's interface
instance Unifiable TypeF where
  zipMatch (TConstF n) (TConstF n') = guard (n == n') >> return (TConstF n)
  zipMatch (TAppF t1 t2) (TAppF t1' t2') = return (TAppF (Right (t1,t1')) (Right (t2,t2')))
  zipMatch (t1 :->: t2) (t1' :->: t2') = return ((Right (t1,t1')) :->: (Right (t2,t2')))
  zipMatch _ _ = Nothing

newtype PropUnify_ v a = PropUnify { runPropUnify :: StateT (Map PVar Bool) Logic a }
  deriving (Alternative, Applicative, Functor, Monad, MonadPlus, MonadState (Map PVar Bool))

type PropUnify = IntBindingT TypeF (PropUnify_ IntVar)

ensureInMap :: (Monad m, Ord k) => m a -> k -> Map k a -> m (a, Map k a)
ensureInMap mv k m = do
  case M.lookup k m of
    Nothing -> do
      v <- mv
      return (v, M.insert k v m)
    Just v -> return (v, m)

assert :: PVar -> Bool -> PropUnify ()
assert p b = do
  (b', m') <- join . lift . gets $ ensureInMap (return b) p
  guard (b == b')
  lift (put m')

generalize :: Type p Var -> PropUnify (Type p IntVar)
generalize t = evalStateT (go t) def where
  go (TypeVar tv) = do
    m <- get
    (uv, m') <- ensureInMap (lift freeVar) tv m
    put m'
    return (TypeVar uv)
  go (TConst n)     = return (TConst n)
  go (PApp p t1 t2) = liftM2 (PApp p) (go t1) (go t2)
  go (TApp t1 t2)   = liftM2 TApp (go t1) (go t2)
  go (t1 :-> t2)    = liftM2 (:->) (go t1) (go t2)

reflectErrors :: (Monad m, Alternative m) => ErrorT e m b -> m b
reflectErrors m = do
  success <- runErrorT m
  case success of
   Left  _ -> empty
   Right t -> return t

(~=) :: UTerm TypeF IntVar -> UTerm TypeF IntVar -> PropUnify (UTerm TypeF IntVar)
a ~= b = reflectErrors (a =:= b)

unify' :: Type PVar Var -> Type PVar Var -> PropUnify (UTerm TypeF IntVar)
unify' t1_ t2_ = do
  u1 <- generalize t1_
  u2 <- generalize t2_
  go u1 u2
  where
  go (TypeVar uv) (TypeVar uv') = UVar uv ~= UVar uv'
  go (TypeVar uv) (TConst  n  ) = UVar uv ~= UTerm (TConstF n)
  go (TypeVar uv) (PApp p t1 t2) = pTrue <|> pFalse where
    pTrue  = do
      assert p True
      v1 <- freeVar
      v2 <- freeVar
      _  <- UVar uv ~= UTerm (TAppF (UVar v1) (UVar v2))
      liftU2 TAppF (go (TypeVar v1) t1) (go (TypeVar v2) t2)
    pFalse = assert p False >> go (TypeVar uv) t2
  go (TypeVar uv) (t1 :-> t2) = do
    v1 <- freeVar
    v2 <- freeVar
    _  <- UVar uv ~= UTerm (UVar v1 :->: UVar v2)
    liftU2 (:->:) (go (TypeVar v1) t1) (go (TypeVar v2) t2)
  go t (TypeVar uv) = go (TypeVar uv) t

  go t@(PApp p t1 t2) t'@(PApp p' t1' t2')
    =   (assert p  False >> go t2 t')
    <|> (assert p' False >> go t t2')
    <|> (assert p True >> assert p' True >> liftU2 TAppF (go t1 t1') (go t2 t2'))
  go (PApp p _ t2) t             = assert p False >> go t2 t
  go t             (PApp p _ t2) = assert p False >> go t t2

  go (t1 :-> t2) (t1' :-> t2') = liftU2 (:->:) (go t1 t1') (go t2 t2')
  go (TConst n)  (TConst n') = guard (n == n') >> return (UTerm (TConstF n))
  go _ _ = empty

liftU1 :: (a ->      TypeF (UTerm TypeF IntVar)) -> PropUnify a ->                PropUnify (UTerm TypeF IntVar)
liftU2 :: (a -> b -> TypeF (UTerm TypeF IntVar)) -> PropUnify a -> PropUnify b -> PropUnify (UTerm TypeF IntVar)
liftU1 = fmap   .   (UTerm .)
liftU2 = liftA2 .  ((UTerm .) .)

solutionsFor :: Type PVar Var -> Type PVar Var -> [UTerm TypeF IntVar]
solutionsFor t1 t2 = observeAll . flip evalStateT def . runPropUnify . evalIntBindingT $ do
  s <- unify' t1 t2
  reflectErrors (applyBindings s)

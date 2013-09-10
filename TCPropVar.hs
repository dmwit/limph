{-# OPTIONS_GHC -Wall #-}

module TCPropVar where

import           Control.Applicative
import           Control.Monad.Supply

type Var  = String
type PVar = Var
type Name = String

data Term
  = Lambda Var Term
  | TermVar Var
  | Term :@ Term
  deriving (Eq, Ord, Show, Read)

data Type p
  = TypeVar Var
  | TConst Name
  | PApp p (Type p) (Type p)
  | TApp (Type p) (Type p)
  | Type p :-> Type p
  deriving (Eq, Ord, Show, Read)

data Constraint
  = T
  | F
  | CVar PVar
  | Neg Constraint
  | Constraint :\/: Constraint
  | Constraint :/\: Constraint
  | Var :==: Type ()
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

unify :: Type PVar -> Type PVar -> M Constraint
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


-- (a -> a) -> a
ty1 = (TypeVar "a" :-> TypeVar "a") :-> TypeVar "a"

-- m_p (b -> m_q c)
ty2 = PApp "p" (TypeVar "m") (TypeVar "b" :-> PApp "q" (TypeVar "m") (TypeVar "c"))

{-
>>> evalSupply (unify ty1 ty2) (map show [0..])
Neg (CVar "p") :/\: ((("b" :==: (TypeVar "0" :-> TypeVar "1")) :/\: (("a" :==: TypeVar "0") :/\: ("a" :==: TypeVar "1"))) :/\: ((CVar "q" :/\: (("a" :==: TApp (TypeVar "2") (TypeVar "3")) :/\: (("2" :==: TypeVar "m") :/\: ("3" :==: TypeVar "c")))) :\/: (Neg (CVar "q") :/\: ("a" :==: TypeVar "c"))))
-}

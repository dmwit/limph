{-# LANGUAGE FlexibleInstances #-}

import Control.Applicative
import Control.Arrow
import Control.Monad.RWS
import Data.Universe

type Variable = String
data Term
	= Lambda Variable Term
	| TermVar Variable
	| Term :@ Term
	deriving (Eq, Ord, Show, Read)

-- TODO: uh... surely the language of monads is richer than this
type MonadVar = String
data MType = MType MonadVar Type
	deriving (Eq, Ord, Show, Read)

data Type
	= TypeVar Variable
	| Type :-> MType
	deriving (Eq, Ord, Show, Read)

data Constraint = MonadVar :> MonadVar deriving (Eq, Ord, Show, Read)
data Scheme = Forall [String] [Constraint] MType deriving (Eq, Ord, Show, Read)
type Context = [(Variable, Scheme)]

newtype Letter = Letter { unLetter :: Char } deriving (Eq, Ord)
instance Universe Letter where universe = map Letter ['a'..'z']
instance Finite   Letter
instance Show Letter where
	showsPrec n = showsPrec n . unLetter
	showList = showList . map unLetter
instance Read Letter where
	readsPrec n = map (first Letter) . readsPrec n
	readList = map (first (map Letter)) . readList

baseSupply = map (map unLetter) (tail universe)

data UnificationConstraint
	= Subsumption Context MType [Constraint] MType
	| Type := Type
	| ScopeError Variable
	deriving (Eq, Ord, Show, Read)

type TC = RWS Context [UnificationConstraint] [String]

infix 7 ==>
infix 7 <==

ea :@ eb <== MType m ta = do
	tb <- eb ==> m
	ea <== MType m (tb :-> MType m ta)

ea <== MType m ta = do
	tb <- ea ==> m
	tb === ta

t1 === t2 = tell [t1 := t2]

TermVar s ==> m = do
	context <- ask
	case lookup s context of
		Nothing -> tell [ScopeError s] >> return (error "lol, I need a better monad")
		Just (Forall vs cs (MType m' t)) -> do
			vs' <- uniques vs
			vt  <- unique
			tell [Subsumption context (MType m (TypeVar vt)) (subst vs' vs cs) (MType (subst vs' vs m') t)]
			return (TypeVar vt)

unique = head <$> uniques [undefined]
uniques vs = do
	(vs', unused) <- gets (splitAt (length vs))
	put unused
	return vs'

subst vs' vs t = foldr (uncurry subst_) t (zip vs' vs)

class Subst a where subst_ :: Variable -> Variable -> a -> a

instance Subst MonadVar where
	subst_ v1 v2 v3
		| v3 == v2  = v1
		| otherwise = v3

instance Subst [Constraint] where
	subst_ v1 v2 = map (\(v3 :> v4) -> subst_ v1 v2 v3 :> subst_ v1 v2 v4)

tc :: Context -> Term -> MType -> [UnificationConstraint]
tc ctxt e mt = case runRWS (e <== mt) ctxt baseSupply of (a, s, w) -> w

-- Okay, this clearly isn't right. Imagine trying to typecheck:
--
-- bool nil nothing :: Maybe [a]
--
-- in the context:
--
-- bool :: a -> a -> a
-- nil :: [a]
-- nothing :: Maybe a
--
-- We can try to write this in the syntax above:
--
-- let ctxt = [("if", Forall ["a"] [] (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a"))))), ("nil", Forall ["b"] [] (MType "[]" (TypeVar "b"))), ("nothing", Forall ["c"] [] (MType "Maybe" (TypeVar "c")))]
--     term = (TermVar "if" :@ TermVar "nil") :@ TermVar "nothing"
--     ty   = MType "Maybe" (TermVar "[d]")
-- in tc ctxt term ty
--
-- But that definition for ty is clearly wrong: it's not a type-level
-- application, and it's got a free (type) variable. The output of tc is:
-- [Subsumption [("if",Forall ["a"] [] (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a")))))
--              ,("nil",Forall ["b"] [] (MType "[]" (TypeVar "b")))
--              ,("nothing",Forall ["c"] [] (MType "Maybe" (TypeVar "c")))
--              ]
--              (MType "Maybe" (TypeVar "b"))
--              []
--              (MType "Maybe" (TypeVar "c"))
-- ,Subsumption [("if",Forall ["a"] [] (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a")))))
--              ,("nil",Forall ["b"] [] (MType "[]" (TypeVar "b")))
--              ,("nothing",Forall ["c"] [] (MType "Maybe" (TypeVar "c")))
--              ]
--              (MType "Maybe" (TypeVar "d"))
--              []
--              (MType "[]" (TypeVar "b"))
-- ,Subsumption [("if",Forall ["a"] [] (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a")))))
--              ,("nil",Forall ["b"] [] (MType "[]" (TypeVar "b")))
--              ,("nothing",Forall ["c"] [] (MType "Maybe" (TypeVar "c")))
--              ]
--              (MType "Maybe" (TypeVar "f"))
--              []
--              (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a"))))
-- ,TypeVar "f" := (TypeVar "d" :-> MType "Maybe" (TypeVar "b" :-> MType "Maybe" (TypeVar "[d]")))]
--
-- the output of trying to check "bool :: a -> a -> Maybe a" in the above context:
-- [Subsumption [("if", Forall ["a"] [] (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a")))))
--              ,("nil", Forall ["b"] [] (MType "[]" (TypeVar "b")))
--              ,("nothing",Forall ["c"] [] (MType "Maybe" (TypeVar "c")))
--              ]
--              (MType "Identity" (TypeVar "b"))
--              []
--              (MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Identity" (TypeVar "a"))))
-- ,TypeVar "b" := (TypeVar "a" :-> MType "Identity" (TypeVar "a" :-> MType "Maybe" (TypeVar "a")))
-- ]

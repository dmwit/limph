module Language.Haskell.TypeCheck.InternalTypes where
-- This module defines the basic types used by the type checker
-- Everything defined in here is exported

import Text.PrettyPrint.HughesPJ
import Data.IORef
import Data.List( nub, intersperse )
import Data.Maybe( fromMaybe )

import Language.Haskell.Exts.Syntax

import Language.Haskell.Exts.Pretty ( Pretty, prettyPrint )

infixr 4 -->    -- The arrow type constructor
-- infixl 4 `App`  -- Application

-----------------------------------
--        Internal Types         --
-----------------------------------

type Sigma = TcType
--type Phi = TcType -- No top-level ForAll binding variables
type Rho = TcType -- No top-level ForAll at all
type Tau = TcType -- No ForAlls anywhere

type Kappa = TcType  -- Representing kinds: Only ->, Star, or meta vars

data TcType = TcForAll [TcTyVarBind] [TcAsst] Rho -- Forall type
            | TcTyFun TcType TcType -- Function type
            | TcTyCon QName -- Type constants
            | TcTyVar TyVar -- Always bound by a ForAll
            | TcTyApp TcType TcType -- Type application
            | MetaTv MetaTv -- A meta type variable
  deriving Eq

data TcAsst = TcClassA QName [Tau]
  deriving (Eq, Show)

type TcCtxt = [TcAsst]

data TcAxiom = TcAxiom [TcTyVarBind] TcCtxt TcAsst
  deriving (Eq, Show)

data TcTyVarBind = TcTyVarBind TyVar Kappa -- forall-bound type variables are explicitly kinded
  deriving (Eq, Show)

unTvBind :: TcTyVarBind -> TyVar
unTvBind (TcTyVarBind t _) = t

data TyVar = BoundTv String        -- A type variable bound by a ForAll
           | SkolemTv String Uniq  -- A skolem constant; the String is
                                   -- just to improve error messages

data MetaTv = Meta Uniq TyRef -- Can unify with any tau-type

type TyRef = IORef (Maybe TcType)
      -- ’Nothing’ means the type variable is not substituted
      -- ’Just ty’ means it has been substituted by ’ty’

instance Eq MetaTv where
    (Meta u1 _) == (Meta u2 _) = u1 == u2

instance Show MetaTv where
    show (Meta u _) = "$$" ++ show u

instance Eq TyVar where
    (BoundTv s1)    == (BoundTv s2)    = s1 == s2
    (SkolemTv _ u1) == (SkolemTv _ u2) = u1 == u2

instance Show TyVar where
    show (BoundTv s) = s
    show (SkolemTv s _) = s

type Uniq = Int

---------------------------------
-- Constructors

(-->) :: Sigma -> Sigma -> Sigma
arg --> res = TcTyFun arg res

(@@) :: Sigma -> Sigma -> Sigma
fun @@ arg = TcTyApp fun arg

con :: String -> Sigma
con = TcTyCon . UnQual . Ident

forAll :: [TcTyVarBind] -> TcCtxt -> Rho -> Sigma
forAll [] [] ty = ty
forAll tvbs cx (TcForAll bndrs ctxt ty) = TcForAll (tvbs ++ bndrs) (cx ++ ctxt) ty
forAll tvbs cx ty = TcForAll tvbs cx ty

isSimple :: Sigma -> Bool
isSimple (TcTyApp t _) = isSimple t
isSimple (TcTyCon _) = True
isSimple _ = False

---------------------------------
-- Free and bound variables

metaTvs :: [TcType] -> [MetaTv]
-- Get the MetaTvs from a type; no duplicates in result
metaTvs tys = foldr go [] tys
    where
      go (MetaTv tv) acc
          | tv `elem` acc = acc
          | otherwise = tv : acc
      go (TcTyVar _) acc = acc
      go (TcTyCon _) acc = acc
      go (TcTyFun arg res) acc = go arg (go res acc)
      go (TcTyApp fun arg) acc = go fun (go arg acc)
      go (TcForAll _ _ ty) acc = go ty acc

-- ForAll binds TyVars only
freeTyVars :: [TcType] -> [TyVar]
-- Get the free TyVars from a type; no duplicates in result
freeTyVars tys = foldr (go []) [] tys
    where
      go :: [TyVar] -- Ignore occurrences of bound type variables
         -> TcType    -- Type to look at
         -> [TyVar] -- Accumulates result
         -> [TyVar]
      go bound (TcTyVar tv) acc
          | tv `elem` bound = acc
          | tv `elem` acc   = acc
          | otherwise       = tv : acc
      go bound (MetaTv _) acc = acc
      go bound (TcTyCon _)  acc = acc
      go bound (TcTyFun arg res) acc = go bound arg (go bound res acc)
      go bound (TcTyApp fun arg) acc = go bound fun (go bound arg acc)
      go bound (TcForAll tvbs _ ty) acc = go (map unTvBind tvbs ++ bound) ty acc  -- TODO: Check for free type vars only appearing in context, e.g. (Foo a b => a -> a)

tyVarBndrs :: Rho -> [TyVar]
-- Get all the binders used in ForAlls in the type, so that
-- when quantifying an outer for-all we can avoid these inner ones
tyVarBndrs ty = nub (bndrs ty)
    where
      bndrs (TcForAll tvbs _ body) = map unTvBind tvbs ++ bndrs body
      bndrs (TcTyFun arg res)     = bndrs arg ++ bndrs res
      bndrs (TcTyApp fun arg)     = bndrs fun ++ bndrs arg
      bndrs _ = []

tyVarName :: TyVar -> String
tyVarName (BoundTv n)    = n
tyVarName (SkolemTv n _) = n
---------------------------------
-- Substitution

type Env = [(TyVar, Tau)]

substTy :: [TyVar] -> [TcType] -> TcType -> TcType
-- Replace the specified quantified type variables by
-- given meta type variables
-- No worries about capture, because the two kinds of type
-- variable are distinct
substTy tvs tys ty = subst_ty (tvs `zip` tys) ty

subst_ty :: Env -> TcType -> TcType
subst_ty env (TcTyFun arg res) = TcTyFun (subst_ty env arg) (subst_ty env res)
subst_ty env (TcTyApp fun arg) = TcTyApp (subst_ty env fun) (subst_ty env arg)
subst_ty env (TcTyVar n) = fromMaybe (TcTyVar n) (lookup n env)
subst_ty env (MetaTv tv) = MetaTv tv
subst_ty env (TcTyCon tc) = TcTyCon tc
subst_ty env (TcForAll ns ctxt rho) = TcForAll ns (subst_ctxt env' ctxt) (subst_ty env' rho)
    where
      env' = [(n,ty') | (n,ty') <- env, not (n `elem` map unTvBind ns)]

substCtxt :: [TyVar] -> [TcType] -> TcCtxt -> TcCtxt
substCtxt tvs tys ctxt = subst_ctxt (tvs `zip` tys) ctxt

subst_ctxt :: Env -> TcCtxt -> TcCtxt
subst_ctxt env = map (subst_asst env)

substAsst :: [TyVar] -> [TcType] -> TcAsst -> TcAsst
substAsst tvs tys asst = head $ substCtxt tvs tys [asst]

subst_asst :: Env -> TcAsst -> TcAsst
subst_asst env (TcClassA qn ts) = TcClassA qn (map (subst_ty env) ts)

-----------------------------------
--          Kinds                --
-----------------------------------

fromSrcKind :: Kind -> Kappa
fromSrcKind sk = case sk of
                   KindStar -> starK
                   KindFn k1 k2 -> TcTyFun (fromSrcKind k1) (fromSrcKind k2)
                   KindParen k -> fromSrcKind k
                   _ -> error "fromSrcKind: unsupported kind"

starK = TcTyCon $ UnQual $ Symbol "*"

-----------------------------------
--    Pretty printing class      --
-----------------------------------

class Outputable a where
    ppr :: a -> Doc

docToString :: Doc -> String
docToString = render

dcolon, dot :: Doc
dcolon = text "::"
dot = char '.'


instance Outputable TcType where
    ppr ty = pprType topPrec ty

instance Outputable MetaTv where
    ppr (Meta u _) = text "$" <> int u

instance Outputable TyVar where
    ppr (BoundTv n)    = text n
    ppr (SkolemTv n u) = text n <+> int u

instance Outputable TcTyVarBind where
    ppr (TcTyVarBind t k) = ppr t -- parens $ sep [ppr t, text "::", ppr k]

instance Show TcType where
    show t = docToString (ppr t)

instance Outputable TcAsst where
    ppr (TcClassA qn ts) = text (prettyPrint qn) <+> hsep (map (pprType atomicPrec) ts)

type Precedence = Int

topPrec, arrPrec, tcPrec, atomicPrec :: Precedence
topPrec = 0 -- Top-level precedence
arrPrec = 1 -- Precedence of (a->b)
tcPrec  = 2 -- Precedence of (T a b)
atomicPrec = 3 -- Precedence of t

precType :: TcType -> Precedence
precType (TcForAll _ _ _) = topPrec
precType (TcTyFun _ _)    = arrPrec
precType (TcTyApp _ _)    = tcPrec
precType _            = atomicPrec

-- All the types are be atomic
pprParendType :: TcType -> Doc
pprParendType ty = pprType tcPrec ty

pprType :: Precedence -> TcType -> Doc
-- Print with parens if precedence arg > precedence of type itself
pprType p ty | p >= precType ty = parens (ppr_type ty)
             | otherwise = ppr_type ty

ppr_type :: TcType -> Doc
-- No parens
ppr_type (TcForAll ns ctxt ty) = sep [text "forall" <+> hsep (map ppr ns) <> dot, ppr_ctxt ctxt, ppr ty]
ppr_type (TcTyFun arg res) = sep [pprType arrPrec arg <+> text "->", pprType (arrPrec-1) res]
ppr_type (TcTyApp fun arg) = sep [pprType tcPrec fun, pprType (tcPrec-1) arg]
ppr_type (TcTyCon qn) =  text $ prettyPrint qn
ppr_type (TcTyVar n) = ppr n
ppr_type (MetaTv tv) = ppr tv

ppr_ctxt :: TcCtxt -> Doc
ppr_ctxt [] = empty
ppr_ctxt as = (parens $ sep $ intersperse (char ',') $ map ppr as) <+> text "=>"

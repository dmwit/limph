{-# LANGUAGE RankNTypes #-}
module Language.Haskell.TypeCheck.Monad where

--import Control.Monad.ST
--import Data.STRef
import Data.IORef

import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ
import Data.List ( (\\), partition )
import Data.Maybe (catMaybes)
import Control.Monad (liftM)
import Control.Applicative ( (<$>))

import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Pretty ( prettyPrint )

import Language.Haskell.TypeCheck.InternalTypes

data TcEnv = TcEnv { 
      uniqs :: IORef Uniq,
      currentMonad :: Maybe Tau,
      vars  :: Map.Map QName (IORef Sigma),
--      cons  :: Map.Map QName (IORef Sigma),
      types :: Map.Map QName (IORef Kappa),
      classes :: Map.Map QName (IORef Kappa),
--      supers  :: Map.Map QName [QName],
      axioms :: [TcAxiom] -- this is where instances go
}

mkEmptyTcEnv :: IO TcEnv
mkEmptyTcEnv = do
  uniqRef <- newIORef 0
  return $ TcEnv {
               uniqs = uniqRef,
               currentMonad = Nothing,
               vars = Map.empty,
               types = Map.empty,
               classes = Map.empty,
--               supers = Map.empty,
               axioms = []
             }

mkTcEnv :: [(QName, Sigma)] -> [(QName, Kappa)] -> [(QName, Kappa)] -> IO TcEnv
mkTcEnv vs ts cs = do
  env <- mkEmptyTcEnv
  vs' <- mapM (\(n,s) -> newIORef s >>= \r -> return (n, r)) vs
  ts' <- mapM (\(n,s) -> newIORef s >>= \r -> return (n, r)) ts
  cs' <- mapM (\(n,s) -> newIORef s >>= \r -> return (n, r)) cs
  return $ env {
               vars = Map.fromList vs',
               types = Map.fromList ts',
               classes = Map.fromList cs'
             }

data Constraint = Constraint

newtype Tc a = Tc (TcEnv -> IO (Either ErrMsg (a, [Constraint])))
unTc :: Tc a -> (TcEnv -> IO (Either ErrMsg (a, [Constraint])))
unTc (Tc a) = a

type ErrMsg = Doc

instance Monad Tc where
  return x = Tc (\_env -> return (Right (x,[])))
  fail err = Tc (\_env -> return (Left (text err)))
  m >>= k = Tc (\env -> do 
                  r1 <- unTc m env
                  case r1 of
                    Left err -> return (Left err)
                    Right (v,cs) -> do
                       x <- unTc (k v) env
                       case x of
                         Left err -> return (Left err)
                         Right (a,cs') -> return (Right (a,cs++cs')))

instance Functor Tc where
  fmap = liftM

failTc :: Doc -> Tc a
-- Fail unconditionally
failTc d = fail (render d)

check :: Bool -> Doc -> Tc ()
check True _ = return ()
check False d = failTc d

solveConstraints :: [Constraint] -> IO (Either ErrMsg ())
solveConstraints cs = return (Right ())

runTc :: TcEnv -> Tc a -> IO (Either ErrMsg a)
runTc env (Tc tc) = do
  x <- tc env
  case x of 
    Left err -> return (Left err)
    Right (a,cs) -> do 
      y <- solveConstraints cs
      case y of
        Left err -> return (Left err)
        Right () -> return (Right a)

lift :: IO a -> Tc a
-- Lift a state transformer action into the typechecker monad
-- ignores the environment and always succeeds
lift st = Tc (\_env -> do { r <- st; return (Right (r,[])) })

newTcRef :: a -> Tc (IORef a)
newTcRef v = lift (newIORef v)

readTcRef :: IORef a -> Tc a
readTcRef r = lift (readIORef r)

writeTcRef :: IORef a -> a -> Tc ()
writeTcRef r v = lift (writeIORef r v)

data Expected a = Infer (IORef a) | Check a

--------------------------------------------------
--      Dealing with constraints                --
--------------------------------------------------
addConstraint :: Constraint -> Tc ()
addConstraint c = Tc (\env -> return (Right ((),[c])))

--------------------------------------------------
--      Dealing with the type environment       --
--------------------------------------------------

getEnv :: Tc TcEnv
getEnv = Tc (\ env -> return (Right (env,[])))

getEnvField :: (TcEnv -> a) -> Tc a
getEnvField f = getEnv >>= return . f

extendEnv :: (TcEnv -> TcEnv) -> Tc a -> Tc a
extendEnv g (Tc m) = Tc (\env -> m (g env))

genRefSnd :: (a, b) -> Tc (a, IORef b)
genRefSnd (a,b) = newTcRef b >>= \r -> return (a, r)

extendVarEnv :: QName -> Sigma -> Tc a -> Tc a
extendVarEnv var ty = extendVarEnvList [(var,ty)]

extendVarEnvList :: [(QName, Sigma)] -> Tc a -> Tc a
extendVarEnvList vartys tca = do
  rtys <- mapM genRefSnd vartys
  extendEnv (extend rtys) tca
    where
      extend rtys env = env { vars = foldl (\acc (var,ty) -> Map.insert var ty acc) (vars env) rtys }

{-
extendConEnv :: QName -> Sigma -> Tc a -> Tc a
extendConEnv con ty = extendConEnvList [(con,ty)]

extendConEnvList :: [(QName, Sigma)] -> Tc a -> Tc a
extendConEnvList contys tca = do
  rtys <- mapM genRefSnd contys
  extendEnv (extend rtys) tca
    where
      extend rtys env = env { cons = foldl (\acc (var,ty) -> Map.insert var ty acc) (cons env) rtys }
-}

extendTypeEnv :: QName -> Kappa -> Tc a -> Tc a
extendTypeEnv var k = extendTypeEnvList [(var,k)]

extendTypeEnvList :: [(QName, Kappa)] -> Tc a -> Tc a
extendTypeEnvList varks tca = do
  rks <- mapM genRefSnd varks
  extendEnv (extend rks) tca
    where
      extend rks env = env { types = foldl (\acc (var,k) -> Map.insert var k acc) (types env) rks }


extendClassEnv :: QName -> Kappa -> Tc a -> Tc a
extendClassEnv var k = extendClassEnvList [(var,k)]

extendClassEnvList :: [(QName, Kappa)] -> Tc a -> Tc a
extendClassEnvList varks tca = do
  rks <- mapM genRefSnd varks
  extendEnv (extend rks) tca
    where
      extend rks env = env { classes = foldl (\acc (var,k) -> Map.insert var k acc) (classes env) rks }


lookupVar :: QName -> Tc Sigma
lookupVar = lookupAux vars

lookupType :: QName -> Tc Kappa
lookupType = lookupAux types

lookupClass :: QName -> Tc Kappa
lookupClass = lookupAux classes

lookupAux :: (TcEnv -> Map.Map QName (IORef a)) -> QName -> Tc a
lookupAux f n = do m <- getEnvField f
                   case Map.lookup n m of
                     Just rty -> readTcRef rty
                     Nothing -> failTc (text "Not in scope:" <+> quotes (text $ prettyPrint n))

getCurrentMonad :: Tc (Maybe Tau)
getCurrentMonad = getEnvField currentMonad


getAxioms :: Tc [TcAxiom]
getAxioms = getEnvField axioms

--------------------------------------------------
--      Creating, reading, writing MetaTvs      --
--------------------------------------------------

newTyVarTy :: Tc Tau
newTyVarTy = do tv <- newMetaTyVar
                return (MetaTv tv)

newMetaTyVar :: Tc MetaTv
newMetaTyVar = do uniq <- newUnique
                  tref <- newTcRef Nothing
                  return (Meta uniq tref)

newSkolemTyVar :: TyVar -> Tc TyVar
newSkolemTyVar tv = do uniq <- newUnique
                       return (SkolemTv (tyVarName tv) uniq)

newPropVar :: Tc Prop
newPropVar = MetaPv <$> newUnique

readTv :: MetaTv -> Tc (Maybe Tau)
readTv (Meta _ ref) = readTcRef ref

writeTv :: MetaTv -> Tau -> Tc ()
writeTv (Meta _ ref) ty = writeTcRef ref (Just ty)

newUnique :: Tc Uniq
newUnique = Tc (\ (TcEnv {uniqs = ref}) ->
                    do uniq <- readIORef ref
                       writeIORef ref (uniq + 1)
                       return (Right (uniq,[])))

newKindVar :: Tc Kappa
newKindVar = newTyVarTy

------------------------------------------
--            Instantiation             --
------------------------------------------

instantiate :: Sigma -> Tc (Rho, TcCtxt)
-- Instantiate the topmost var binders of the argument type
-- with flexible type variables.
-- Result is a Rho, which can be a top-level forall with no binders
instantiate (TcForAll tvbs ctxt ty)
  = do tvs' <- mapM (\_ -> newMetaTyVar) tvbs
       let tvs = map unTvBind tvbs
           mts = map MetaTv tvs'
           ty' = substTy tvs mts ty
           ctxt' = substCtxt tvs mts ctxt
       return $ (ty', ctxt')
instantiate ty = return (ty, [])

skolemise :: Sigma -> Tc ([TyVar], TcCtxt, Rho)
-- Performs deep skolemisation, returning the
-- skolem constants, the skolemised context and the skolemised type
skolemise (TcForAll tvbs ctxt ty)
    -- Rule PRPOLY
    = do let tvs = map unTvBind tvbs
         sks1 <- mapM newSkolemTyVar tvs
         let sktvs = map TcTyVar sks1
         (sks2, ctxt2, ty') <- skolemise (substTy tvs sktvs ty)
         let ctxt' = substCtxt tvs sktvs ctxt
         return (sks1 ++ sks2, ctxt' ++ ctxt2, ty')
skolemise (TcTyFun arg_ty res_ty)
    -- Rule PRFUN
    = do (sks, ctxt, res_ty') <- skolemise res_ty
         return (sks, ctxt, TcTyFun arg_ty res_ty')
skolemise ty
    -- Rule PRMONO
    = return ([], [], ty)

instantiateAxiom :: TcAxiom -> Tc (TcAsst, TcCtxt)
instantiateAxiom (TcAxiom tvbs ctxt asst)
  = do tvs' <- mapM (\_ -> newMetaTyVar) tvbs
       let tvs = map unTvBind tvbs
           mts = map MetaTv tvs'
           asst' = substAsst tvs mts asst
           ctxt' = substCtxt tvs mts ctxt
       return $ (asst', ctxt')


------------------------------------------
--            Quantification            --
------------------------------------------
quantify :: [MetaTv] -> TcCtxt -> Rho -> Tc Sigma
-- Quantify over the specified type variables (all flexible with unknown kinds)
quantify tvs ctxt ty
    = do mapM_ bind (tvs `zip` new_bndrs)    -- 'bind' is just a cunning way
         ty' <- zonkType ty                  -- of doing the substitution
         ctxt' <- zonkCtxt ctxt
         kvs <- mapM (\_ -> newKindVar) tvs
         return (forAll (map (uncurry TcTyVarBind) (new_bndrs `zip` kvs)) ctxt' ty')
  where
    used_bndrs = tyVarBndrs ty -- Avoid quantified type variables in use
    new_bndrs = take (length tvs) (allBinders \\ used_bndrs)
    bind (tv, name) = writeTv tv (TcTyVar name)

allBinders :: [TyVar] -- a,b,..z, a1, b1,... z1, a2, b2,...
allBinders = [ BoundTv [x] | x <- ['a'..'z'] ] ++
               [ BoundTv (x : show i) | i <- [1 :: Integer ..], x <- ['a'..'z']]

prefBinders :: String -> [TyVar]
prefBinders str = BoundTv str : [ BoundTv (str ++ show i) | i <- [1 :: Integer ..]]

------------------------------------------
--       Getting the free tyvars        --
------------------------------------------

getEnvTypes :: Tc [Sigma]
-- Get the types mentioned in the environment
getEnvTypes = do env <- getEnvField vars
                 mapM readTcRef (Map.elems env)

getMetaTyVars :: [TcType] -> Tc [MetaTv]
-- This function takes account of zonking, and returns a set
-- (no duplicates) of unbound meta-type variables
getMetaTyVars tys = do tys' <- mapM zonkType tys
                       return (metaTvs tys')

getFreeTyVars :: [TcType] -> Tc [TyVar]
-- This function takes account of zonking, and returns a set
-- (no duplicates) of free type variables
getFreeTyVars tys = do tys' <- mapM zonkType tys
                       return (freeTyVars tys')

------------------------------------------
--                Zonking               --
-- Eliminate any substitutions in the type
------------------------------------------

zonkType :: TcType -> Tc TcType
zonkType = zonkType' False

zonkType' :: Bool -> TcType -> Tc TcType

zonkType' i (TcForAll ns ctxt ty) = do ty' <- zonkType' i ty
                                       ctxt' <- zonkCtxt ctxt
                                       return (TcForAll ns ctxt' ty')
zonkType' i (TcTyFun arg res) = do arg' <- zonkType' i arg
                                   res' <- zonkType' i res
                                   return (TcTyFun arg' res')
zonkType' i (TcTyApp fun arg) = do fun' <- zonkType' i fun
                                   arg' <- zonkType' i arg
                                   return (TcTyApp fun' arg')
zonkType' _ (TcTyCon tc)  = return (TcTyCon tc)
zonkType' _ (TcTyVar n)   = return (TcTyVar n)
zonkType' i (MetaTv tv) 
    -- A mutable type variable
    = do mb_ty <- readTv tv
         case mb_ty of
           Nothing -> if i
                       -- When we zonk for kinds, all remaining kind vars must be fixed to *
                       then writeTv tv starK >> return starK
                       else return (MetaTv tv)
           Just ty -> do ty' <- zonkType ty
                         writeTv tv ty' -- "Short out" multiple hops
                         return ty'

zonkInstKind :: TcType -> Tc TcType
zonkInstKind = zonkType' True

-- Kinds never have contexts, hence no Bool parameter
zonkCtxt :: TcCtxt -> Tc TcCtxt
zonkCtxt = mapM zonkAsst

zonkAsst :: TcAsst -> Tc TcAsst
zonkAsst (TcClassA qn ts) = do
  ts' <- mapM zonkType ts
  return $ TcClassA qn ts'

zonkKindEnvs :: Tc ()
zonkKindEnvs = do
  typs <- getEnvField types
  clss <- getEnvField classes
  mapM_ zonkIt (Map.elems typs ++ Map.elems clss)

      where zonkIt :: IORef TcType -> Tc ()
            zonkIt ref = do ty <- readTcRef ref
                            ty' <- zonkInstKind ty
                            writeTcRef ref ty'
  
zonkVarEnv :: [(QName, TcType)] -> Tc [(QName, TcType)]
zonkVarEnv [] = return []
zonkVarEnv ((n,ty):ve) = do ty' <- zonkType ty
                            ve' <- zonkVarEnv ve
                            return $ (n,ty') : ve'

------------------------------------------
--             Unification              --
------------------------------------------

unify :: Tau -> Tau -> Tc ()
unify ty1 ty2 | badType ty1 || badType ty2 -- Compiler error
                  = failTc (text "Panic! Unexpected types in unification:" <+> vcat [ppr ty1, ppr ty2])
unify (TcTyVar tv1) (TcTyVar tv2) | tv1 == tv2 = return ()
unify (MetaTv tv1) (MetaTv tv2) | tv1 == tv2 = return ()
unify (MetaTv tv) ty = unifyVar tv ty
unify ty (MetaTv tv) = unifyVar tv ty

unify (TcTyFun arg1 res1) (TcTyFun arg2 res2)
    = do unify arg1 arg2
         unify res1 res2
unify (TcTyApp fun1 arg1) (TcTyFun fun2 arg2)
    = do unify fun1 fun2
         unify arg1 arg2
unify (TcTyCon tc1) (TcTyCon tc2) | tc1 == tc2 = return ()
unify ty1 ty2 = failTc (text "Cannot unify types:" <+> vcat [ppr ty1, ppr ty2])


-----------------------------------------

unifyVar :: MetaTv -> Tau -> Tc ()
-- Invariant: tv1 is a flexible type variable
unifyVar tv1 ty2
    -- Check whether tv1 is bound
    = do mb_ty1 <- readTv tv1
         case mb_ty1 of
           Just ty1 -> unify ty1 ty2
           Nothing -> unifyUnboundVar tv1 ty2

unifyUnboundVar :: MetaTv -> Tau -> Tc ()
-- Invariant: the flexible type variable tv1 is not bound
unifyUnboundVar tv1 ty2@(MetaTv tv2)
    = do -- We know that tv1 /= tv2 (else the
         -- top case in unify would catch it)
         mb_ty2 <- readTv tv2
         case mb_ty2 of
           Just ty2' -> unify (MetaTv tv1) ty2'
           Nothing -> writeTv tv1 ty2
unifyUnboundVar tv1 ty2
    = do tvs2 <- getMetaTyVars [ty2]
         if tv1 `elem` tvs2 
          then occursCheckErr tv1 ty2
          else writeTv tv1 ty2

-----------------------------------------

unifyFun :: Rho -> Tc (Prop,Sigma, Prop,Rho)
unifyFun tau = do mm <- getCurrentMonad
                  case mm of
                    Nothing -> do (arg,res) <- unifyPlainFun tau
                                  return (PropFalse, arg, PropFalse, res)
                    Just m -> unifyMonFun m tau

unifyMonFun :: Tau -> Rho -> Tc (Prop,Sigma, Prop,Rho)
-- (p,arg,q,res) <- unifyFun m fun
-- unifies 'fun' with 'm_p (arg -> m_q res)'
unifyMonFun m (TcTyFun arg res) 
    = do q <- newPropVar
         res_ty <- newTyVarTy
         unify res (TcTyMApp q m res_ty)
         return (PropFalse, arg, q, res_ty)
unifyMonFun m tau
    = do p <- newPropVar
         arg_ty <- newTyVarTy
         q <- newPropVar
         res_ty <- newTyVarTy
         unify tau (TcTyMApp p m (arg_ty --> (TcTyMApp q m res_ty)))
         return (p, arg_ty, q, res_ty)


unifyPlainFun :: Rho -> Tc (Sigma, Rho)
-- (arg,res) <- unifyFun fun
-- unifies 'fun' with '(arg -> res)'
unifyPlainFun (TcTyFun arg res) = return (arg,res)
unifyPlainFun tau
    = do arg_ty <- newTyVarTy
         res_ty <- newTyVarTy
         unify tau (arg_ty --> res_ty)
         return (arg_ty, res_ty)

unifyMonadic :: Rho -> Tc (Rho, TcCtxt)
-- (res,Q) <- unifyMonadic gen
-- unifies 'gen' with 'Monad m => m res', where Q == [Monad m]
unifyMonadic (TcTyApp tyM tyA) = return (tyA, monadQ tyM)
unifyMonadic tau
    = do monadTy <- newTyVarTy
         resTy   <- newTyVarTy
         unify tau (TcTyApp monadTy resTy)
         return (resTy, monadQ monadTy)

monadQ :: Rho -> TcCtxt
monadQ ty = [TcClassA (UnQual $ Ident "Monad") [ty]]
  
  

-----------------------------------------

occursCheckErr :: MetaTv -> Tau -> Tc ()
-- Raise an occurs-check error
occursCheckErr tv ty 
    = failTc (text "Occurs check for" <+> quotes (ppr tv) <+> text "in:" <+> ppr ty)

badType :: Tau -> Bool
-- Tells which types should never be encountered during unification
badType (TcTyVar (BoundTv _)) = True
badType _ = False

-------------------------------------
-- Translating from parse entities --
-------------------------------------

fromSrcType :: Type -> Tc Sigma
fromSrcType t = do
  (tcty, subst) <- fromSrcType' t []
  let qs = snd $ unzip subst -- these variables were not explicitly quantified in the source
  if null qs then return tcty else quantify qs [] tcty
  
-- Invariant: All the MetaTv in the substitution are fully flexible
fromSrcType' :: Type -> [(Name, MetaTv)] -> Tc (Sigma, [(Name, MetaTv)])
fromSrcType' (TyVar n) subst =
    case lookup n subst of
      Just mTv -> return (MetaTv mTv, subst)
      Nothing -> do
        mTv <- newMetaTyVar -- Invariant preserved, we don't write to mTv
        return (MetaTv mTv, (n,mTv):subst)
fromSrcType' (TyForall mtvbs ctxt ty) subst = do
  let tvns = maybe [] (map tvbName) mtvbs
      (subst0, substShadow) = partition ((`elem` tvns) . fst) subst -- should go away when we do a name conversion pass first
  (tcty, subst1) <- fromSrcType' ty subst0
  (tcctxt, subst2) <- fromSrcCtxt' ctxt subst1
  let qs = catMaybes $ map (flip lookup subst2) tvns
  ty' <- quantify qs tcctxt tcty
  return (ty', filter ((`elem` tvns) . fst) subst2 ++ substShadow)
fromSrcType' (TyFun arg res) subst = do
  (argTy, subst1) <- fromSrcType' arg subst
  (resTy, subst2) <- fromSrcType' res subst1
  return (argTy --> resTy, subst2)
fromSrcType' (TyTuple Boxed ts) subst =
  let k = length ts 
      con = TyCon $ Special $ TupleCon Boxed k
      t = foldl TyApp con ts
  in fromSrcType' t subst
fromSrcType' (TyList t) subst = 
    let con = TyCon $ Special $ ListCon
    in fromSrcType' (TyApp con t) subst
fromSrcType' (TyApp fun arg) subst = do
    (funTy, subst1) <- fromSrcType' fun subst
    (argTy, subst2) <- fromSrcType' arg subst1
    return (TcTyApp funTy argTy, subst2)
fromSrcType' (TyCon qn) subst = return (TcTyCon qn, subst)
fromSrcType' (TyParen t) subst = fromSrcType' t subst
fromSrcType' (TyInfix t1 qn t2) subst = fromSrcType' (TyApp (TyApp (TyCon qn) t1) t2) subst
fromSrcType' (TyKind t k) subst = fromSrcType' t subst -- TODO: We clearly need explicit kinds in the Tc world as well.

fromSrcCtxt' :: Context -> [(Name, MetaTv)] -> Tc (TcCtxt, [(Name, MetaTv)])
fromSrcCtxt' [] subst = return ([], subst)
fromSrcCtxt' (a:as) subst = do
  (tca, subst') <- fromSrcAsst a subst
  (tcas, subst'') <- fromSrcCtxt' as subst'
  return (tca:tcas, subst'')

fromSrcAsst :: Asst -> [(Name, MetaTv)] -> Tc (TcAsst, [(Name, MetaTv)])
fromSrcAsst (ClassA qn ts) subst = do
  (tcts, subst') <- fromSrcTypes ts subst
  return (TcClassA qn tcts, subst')

fromSrcTypes :: [Type] -> [(Name, MetaTv)] -> Tc ([TcType], [(Name, MetaTv)])
fromSrcTypes [] subst = return ([], subst)
fromSrcTypes (t:ts) subst = do
  (tct, subst1) <- fromSrcType' t subst
  (tcts, subst2) <- fromSrcTypes ts subst1
  return (tct:tcts, subst2)

tvbName :: TyVarBind -> Name
tvbName (UnkindedVar n) = n
tvbName (KindedVar n _) = n


debugShow s = lift $ putStrLn $ "DEBUG: " ++ s
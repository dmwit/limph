module Language.Haskell.TypeCheck.TypeCheck where

import Language.Haskell.TypeCheck.InternalTypes
import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.Simplify

import Language.Haskell.Exts

import Text.PrettyPrint.HughesPJ
import Data.List ( (\\), partition, unzip4 )
import Control.Applicative ( (<$>) )

----------------------------------------------
--     The top-level expression checker     --
----------------------------------------------

typecheckExp :: Exp -> Tc Sigma
typecheckExp e = do 
--  debugShow "Starting..."
  ty <- inferSigma e
--  debugShow "Top-level type inferred"
  zonkType ty

typecheckModule :: Module -> Tc VarEnv
typecheckModule (Module _ _ _ _ _ _ ds) = do
  (ve, qRem, _) <- tcBindGroup ds
  case qRem of
    [] -> return ve
    q  -> fail $ "Unsolved assertions: " ++ show q
  

type Q = TcCtxt

type VarEnv = [(QName, Sigma)]

----------------------------------------------
--       Expressions with rho types         --
----------------------------------------------

-- Invariant: The Phi is in weak-prenex form
checkRho :: Exp -> Rho -> Tc Q
checkRho e ty = tcRho e (Check ty)

inferRho :: Exp -> Tc (Rho, Q)
inferRho e = do
  ref <- newTcRef (error "inferRho: empty result")
  q   <- tcRho e (Infer ref)
  ty  <- readTcRef ref
  return (ty, q)


tcRho :: Exp -> Expected Rho -> Tc Q
-- Literals
tcRho (Lit l) expTy = do 
  lTy <- litType l
  instSigma lTy expTy

-- Variables: Rule VARCON (a)
tcRho (Var qn) expTy = do
  sigma <- lookupVar qn
  instSigma sigma expTy

-- Constructors: Rule VARCON (b)
tcRho (Con qn) expTy = do
  sigma <- lookupVar qn
  instSigma sigma expTy

-- Application: Rule APP
tcRho (App fun arg) expTy = do
  (funTy, qfun) <- inferRho fun
  (argTy, resTy) <- unifyFun funTy
  qarg <- checkSigma arg argTy
  q <- instSigma resTy expTy
  return $ qfun ++ qarg ++ q

-- Lambda abstraction (infer): Rule ABS1
tcRho (Lambda _ ps body) (Infer ref) = do
  (tys, ve, qReq, qDis) <- inferPats ps
  extendVarEnvList ve $ do
    (resTy, qe) <- inferRho body
    let lamTy = foldr (-->) resTy tys
    writeTcRef ref lamTy
    qRes <- simplify (qReq ++ qDis) qe
    return (qReq ++ qRes)

-- Lambda abstraction (check): Rule ABS2
tcRho (Lambda _ ps body) (Check ty) = do
  (resTy, ve, qReq, qDis) <- unifyFunPats ty ps
  extendVarEnvList ve $ do
    qE <- checkRho body resTy
    qRes <- simplify (qReq ++ qDis) qE
    return (qReq ++ qRes)

-- Case distinction: Rule CASE
tcRho (Case e alts) (Check ty) = do
  (eTy, qE) <- inferRho e
  qSs <- mapM (\alt -> checkAlt alt (eTy --> ty)) alts
  return (qE ++ concat qSs)

tcRho (Case e alts) (Infer ref) = do
--  (eTy, qE) <- inferRho e
  (tysAs, qSs) <- unzip <$> mapM (\alt -> inferAlt alt) alts
  qDsk <- subsCheckAll tysAs
  (argTy, resTy) <- unifyFun (head tysAs)
  qE <- checkRho e argTy
  writeTcRef ref resTy
  return (qE ++ concat qSs ++ qDsk)

-- Let-binding: Rule LET
tcRho (Let binds e) expTy = do
  (ve, qReq, qDis) <- tcBinds binds
  -- debugShow (show ve)
  extendVarEnvList ve $ do
    qE <- tcRho e expTy
    qRes <- simplify (qReq ++ qDis) qE
    return (qReq ++ qRes)

-- Conditionals: Rule IF1 (infer)
tcRho (If cond th el) (Infer ref) = do
  qC <- checkRho cond boolType
  (rho1, qT) <- inferRho th
  (rho2, qE) <- inferRho el
  qDsk <- subsCheckAll [rho1,rho2]
  writeTcRef ref rho1
  return (qC ++ qT ++ qE ++ qDsk)

-- Conditionals: Rule IF2 (check)
tcRho (If cond th el) (Check ty) = do
  qC <- checkRho cond boolType
  qT <- checkRho th ty
  qE <- checkRho el ty
  return (qC ++ qT ++ qE)

-- Do-blocks: Rule DO
tcRho (Do stmts) expTy = checkStmts stmts expTy

-- Parentheses: Rule PAREN
tcRho (Paren e) expTy = tcRho e expTy

-- Explicit type sigs: Rule EXPTYPESIG
tcRho (ExpTypeSig _ e t) expTy = do
  ty <- fromSrcType t
  qE <- checkRho e ty
  qI <- instSigma ty expTy
  return (qE ++ qI)

tcRho e _ = fail $ "Unsupported expression: " ++ prettyPrint e

-- List comprehensions: Rule LISTCOMP
--tcRho (ListComp e qstmts) expTy = do
  
  

-- Left H98: InfixApp, sections, recs, enums, ListComp, NegApp


---------------------------------------
-- Checking case alternatives 

checkAlt :: Alt -> Rho -> Tc Q
checkAlt alt ty = tcAlt alt (Check ty)

inferAlt :: Alt -> Tc (Rho, Q)
inferAlt alt = do
  ref <- newTcRef $ error "inferAlt: empty result"
  q <- tcAlt alt (Infer ref)
  resTy <- readTcRef ref
  return (resTy, q)

tcAlt :: Alt -> Expected Rho -> Tc Q
tcAlt (Alt _ p galts whereBinds) expTy = tcAltMatch [p] galts whereBinds expTy

checkAltMatch :: [Pat] -> GuardedAlts -> Binds -> Rho -> Tc Q
checkAltMatch ps galts bs ty = tcAltMatch ps galts bs (Check ty)

inferAltMatch :: [Pat] -> GuardedAlts -> Binds -> Tc (Rho, Q)
inferAltMatch ps galts bs = do
  ref <- newTcRef $ error "inferAltMatch: empty result"
  q <- tcAltMatch ps galts bs (Infer ref)
  ty <- readTcRef ref
  return (ty, q)

tcAltMatch :: [Pat] -> GuardedAlts -> Binds -> Expected Rho -> Tc Q
tcAltMatch ps galts whereBinds expTy = do
  (tysPs, ve, qReq, qDis) <- inferPats ps
  extendVarEnvList ve $ do
    (veB, qReqB, qDisB) <- tcBinds whereBinds
    qResB <- simplify (qReq ++ qDis) qReqB
    extendVarEnvList veB $ do
      (tyA, qA) <- inferGuardedAlts galts (qReq ++ qDis ++ qResB ++ qDisB)
      let tyAM = foldr (-->) tyA tysPs
      qI <- instSigma tyAM expTy
      qRes <- simplify (qReq ++ qDis ++ qResB ++ qDisB ++ qA) qI
      return (qReq ++ qResB ++ qA ++ qRes)
  
checkGuardedAlts :: GuardedAlts -> Q -> Rho -> Tc Q
checkGuardedAlts galts qDis resTy = tcGuardedAlts galts qDis (Check resTy)

inferGuardedAlts :: GuardedAlts -> Q -> Tc (Rho, Q)
inferGuardedAlts galts qDis = do
  ref <- newTcRef $ error "inferAlt: empty result"
  q <- tcGuardedAlts galts qDis (Infer ref)
  resTy <- readTcRef ref
  return (resTy, q)

tcGuardedAlts :: GuardedAlts -> Q -> Expected Rho -> Tc Q
tcGuardedAlts (UnGuardedAlt e) qDis expTy = do
  qE <- tcRho e expTy
  simplify qDis qE

tcGuardedAlts (GuardedAlts galts) qDis (Check ty) = do
  qAs <- mapM (\galt -> checkGuardedAlt galt qDis ty) galts
  return $ concat qAs

tcGuardedAlts (GuardedAlts galts) qDis (Infer ref) = do
  (tysAs, qAs) <- unzip <$> mapM (\galt -> inferGuardedAlt galt qDis) galts
  qDsk <- subsCheckAll tysAs
  writeTcRef ref (head tysAs)
  qRes <- simplify (qDis ++ concat qAs) qDsk
  return (concat qAs ++ qRes)


checkGuardedAlt :: GuardedAlt -> Q -> Rho -> Tc Q
checkGuardedAlt galt qDis ty = tcGuardedAlt galt qDis (Check ty)

inferGuardedAlt :: GuardedAlt -> Q -> Tc (Rho, Q)
inferGuardedAlt galt qDis = do
  ref <- newTcRef $ error "inferGuardedAlt: empty result"
  q <- tcGuardedAlt galt qDis (Infer ref)
  ty <- readTcRef ref
  return (ty, q)

tcGuardedAlt :: GuardedAlt -> Q -> Expected Rho -> Tc Q
tcGuardedAlt (GuardedAlt _ guards e) qDis expTy = do
  (veG, qReqG, qDisG) <- checkGuards guards
  qResG <- simplify qDis qReqG
  extendVarEnvList veG $ do
    qE <- tcRho e expTy
    qRes <- simplify (qDis ++ qDisG ++ qResG) qE
    return (qRes ++ qResG)


----------------------------------------------
-- Checking statements in various forms.
-- Different judgments are needed since the typing
-- requirements differ between all three forms.

checkGuards :: [Stmt] -> Tc (VarEnv, Q, Q)
checkGuards = go [] [] []
    where go :: VarEnv -> Q -> Q -> [Stmt] -> Tc (VarEnv, Q, Q)
          go accVe accQreq accQdis [] = return (accVe, accQreq, accQdis)
          go accVe accQreq accQdis (g:gs) = do
            (veG, qReqG, qDisG) <- checkGuard g
            qRes <- simplify (accQreq ++ accQdis) qReqG
            extendVarEnvList veG $
              go (accVe ++ veG) (accQreq ++ qRes) (accQdis ++ qDisG) gs

checkGuard :: Stmt -> Tc (VarEnv, Q, Q)
checkGuard (Qualifier e) = do
  q <- checkRho e boolType
  return ([], q, [])
checkGuard (Generator _ p e) = do
  (ty, ve, qReq, qDis) <- inferPat p
  qE <- checkSigma e ty
  qRes <- simplify (qReq ++ qDis) qE
  return (ve, qReq ++ qRes, qDis)
-- checkGuard (LetStmt bs) = tcBinds bs
checkGuard _ = fail "Unsupported guard"

checkStmts :: [Stmt] -> Expected Rho -> Tc Q
checkStmts = go [] []
    where go :: Q -> Q -> [Stmt] -> Expected Rho -> Tc Q
          go _ _ [] _ = fail $ "The last statement in a do-block must be an expression"
          go accQreq accQdis [Qualifier e] expTy = do
            qE <- tcRho e expTy
            qRes <- simplify (accQreq ++ accQdis) qE
            return (accQreq ++ qRes)
          go accQreq accQdis (s:ss) expTy = do
            (ve, qReq, qDis) <- checkStmt s
            qRes <- simplify (accQreq ++ accQdis) qReq
            extendVarEnvList ve $ 
              go (accQreq ++ qRes) (accQdis ++ qDis) ss expTy

checkStmt :: Stmt -> Tc (VarEnv, Q, Q)
checkStmt (Qualifier e) = do
  (_,q) <- inferRho e
  return ([], q, [])
checkStmt (Generator _ p e) = do
  (ty, ve, qReq, qDis) <- inferPat p
  (retTy, qMon) <- unifyMonadic ty
  qE <- checkSigma e retTy
  qRes <- simplify (qReq ++ qDis) (qE ++ qMon)
  return (ve, qReq ++ qRes, qDis)
checkStmt (LetStmt bs) = tcBinds bs
checkStmt _ = fail "Unsupported stmt"



-----------------------------------------------
-- Literals
-----------------------------------------------

litType :: Literal -> Tc Sigma
litType (Char _) = return charType
litType (Int _)  = numType
litType (Frac _) = fracType
litType (String _) = return stringType

charType = TcTyCon (UnQual $ Ident "Char")
boolType = TcTyCon (UnQual $ Ident "Bool")
-- A lazy but convenient way of generating the Num type
numType = mkPredType (UnQual $ Ident "Num")
fracType = mkPredType (UnQual $ Ident "Fractional")
stringType = listType charType

listCon = TcTyCon $ Special ListCon
listType t = listCon @@ t

mkPredType qn = do
  mtv <- newMetaTyVar
  let mty = MetaTv mtv
      pred = TcClassA qn [mty]
  quantify [mtv] [pred] mty

----------------------------------------------
--       Expressions with polytypes         --
----------------------------------------------


inferSigma :: Exp -> Tc Sigma
inferSigma e = do
  (expTy, q) <- inferRho e
  qres <- simplify [] q -- Can only remove axiomatic constraints, e.g. Eq Int
  envTys <- getEnvTypes
  envTvs <- getMetaTyVars envTys
  resTvs <- getMetaTyVars [expTy]
  let forallTvs = resTvs \\ envTvs
  quantify forallTvs qres expTy


checkSigma :: Exp -> Sigma -> Tc Q
checkSigma e sigma = do
  (skols, ctxt, rho) <- skolemise sigma
  q <- checkRho e rho
  qres <- simplify ctxt q
  envTys <- getEnvTypes
  escTvs <- getFreeTyVars (sigma: envTys)
  let badTvs = filter (`elem` escTvs) skols
  check (null badTvs) (text "Type not polymorphic enough")
  return qres


----------------------------------------------
--          Typing patterns                 --
----------------------------------------------

tcPats :: [Pat] -> [Expected Sigma] -> Tc (VarEnv, Q, Q)
tcPats ps expTys = do
  veqs <- mapM (uncurry tcPat) (zip ps expTys)
  -- We assume that name resolution has been done,
  -- so we don't need to check the validity of bound
  -- variables in the env.
  let (ves, qsReq, qsDis) = unzip3 veqs
  return (concat ves, concat qsReq, concat qsDis)

inferPats :: [Pat] -> Tc ([Sigma], VarEnv, Q, Q)
inferPats ps = do
  refs <- mapM (\_ -> newTcRef (error "inferPats: empty result")) ps
  (ve, qReq, qDis) <- tcPats ps (map Infer refs)
  tys <- mapM readTcRef refs
  return (tys, ve, qReq, qDis)

checkPats :: [Pat] -> [Sigma] -> Tc (VarEnv, Q, Q)
checkPats ps tys = tcPats ps (map Check tys)

inferPat :: Pat -> Tc (Sigma, VarEnv, Q, Q)
inferPat p = do
  ref <- newTcRef (error "inferPat: empty result")
  (ve, qReq, qDis) <- tcPat p (Infer ref)
  ty <- readTcRef ref
  return (ty, ve, qReq, qDis)

checkPat :: Pat -> Sigma -> Tc (VarEnv, Q, Q)
checkPat p ty = tcPat p (Check ty)

tcPat :: Pat -> Expected Sigma -> Tc (VarEnv, Q, Q)

tcPat (PVar n) expTy = do
  -- No lookup - this is a definition!
  ty <- newTyVarTy
  q <- instSigma ty expTy
  return ([(UnQual n, ty)], q, [])

tcPat (PLit lit) expTy = do
  lTy <- litType lit
  q <- instSigma lTy expTy
  return ([], q, [])

tcPat (PWildCard) expTy = do
  ty <- newTyVarTy
  q <- instSigma ty expTy -- q will be []
  return ([], q, [])

tcPat (PApp k ps) expTy = do
  kty <- lookupVar k
  (krho, kq) <- instantiate kty
  (resTy, ve, qReq, qDis) <- unifyFunPats krho ps
  -- The result type must be a type constructor
  check (isSimple resTy) $ text $ "tcPat: Constructor given too few parameters: " ++ prettyPrint k
  qc <- instSigma resTy expTy
  qRes <- simplify kq qReq
  return (ve, qRes ++ qc, kq ++ qDis)

tcPat (PIrrPat p) expTy = tcPat p expTy

tcPat (PAsPat n p) (Infer r) = do
  (ty, ve, qReq, qDis) <- inferPat p
  writeTcRef r ty
  return ((UnQual n, ty) : ve, qReq, qDis)
tcPat (PAsPat n p) (Check ty) = do
  (ve, qReq, qDis) <- checkPat p ty
  return ((UnQual n, ty) : ve, qReq, qDis)

tcPat (PParen p) expTy = tcPat p expTy

tcPat (PatTypeSig _ p srcTy) (Infer r) = do
  ty <- fromSrcType srcTy
  writeTcRef r ty
  checkPat p ty  
tcPat (PatTypeSig _ p srcTy) (Check ty) = do
  ty' <- fromSrcType srcTy
  q1 <- subsCheck ty ty'
  (ve, qReq, qDis) <- checkPat p ty'
  return (ve, q1 ++ qReq, qDis)

-- Remaining H98: PNeg, PNPlusK, PInfixApp, PTuple, PList, PRec

unifyFunPats :: Rho -> [Pat] -> Tc (Tau, VarEnv, Q, Q)
unifyFunPats = go [] [] []
    where go :: VarEnv -> Q -> Q -> Rho -> [Pat] -> Tc (Tau, VarEnv, Q, Q)
          go accVe accQreq accQdis tau [] = return (tau, accVe, accQreq, accQdis)
          go accVe accQreq accQdis rho (p:ps) = do
            (argTy, resTy) <- unifyFun rho
            (ve, qReq, qDis) <- checkPat p argTy
            go (ve ++ accVe) (qReq ++ accQreq) (qDis ++ accQdis) resTy ps

----------------------------------------------
--         Typing bind groups               --
----------------------------------------------

tcBinds :: Binds -> Tc (VarEnv, Q, Q)
tcBinds (BDecls ds) = tcBindGroup ds

-- Invariant: ds contains only TypeSig, PatBind and FunBind
tcBindGroup :: [Decl] -> Tc (VarEnv, Q, Q)
tcBindGroup ds = do
  let explTs = [ (n, t) | TypeSig _ ns t <- ds, n <- ns ]
  explSigs <- mapM (\(n,t) -> fromSrcType t >>= \ty -> return (n,ty)) explTs
  let (expls, impps) = partition (isExplTyped $ map fst explSigs) ds
      (impls, ipsts) = partition isImplTyped impps
      pbinds = [ pb | pb@(PatBind {}) <- ipsts ]
  impTvs <- mapM (\_ -> newTyVarTy) impls -- Bind variables for the implicits
  let implSigs = [ (n, tv) | (FunBind ms, tv) <- zip impls impTvs, 
                                    let Match _ n _ _ _ _ = head ms ]  
  let ve = (map (\(n,s) -> (UnQual n, s)) $ explSigs ++ implSigs)
  extendVarEnvList ve $ do
    -- Now we start in the reverse, with the pattern bindings
    (vePB, qReqPB, qDisPB) <- tcPatBinds pbinds
    extendVarEnvList vePB $ do
      -- Now we have bindings for every top-level name
      qs <- mapM tcVarBind (impls ++ expls)
      ve' <- zonkVarEnv (ve ++ vePB)
      qRes <- simplify (qReqPB ++ qDisPB) (concat qs)
      return (ve', qReqPB ++ qRes, qDisPB)

-- Invariant: All argument decls are PatBind
tcPatBinds :: [Decl] -> Tc (VarEnv, Q, Q)
tcPatBinds ds = do
  let (plts, rhsbinds) = unzip [ ((p, l, mt), (rhs, binds)) | PatBind l p mt rhs binds <- ds ]
      mkPat (p,_,Nothing) = p
      mkPat (p,l,Just t) = PatTypeSig l p t
      ps = map mkPat plts
  (tys, ve, qReq, qDis) <- inferPats ps
  extendVarEnvList ve $ do
    (tys', qsRhs) <- unzip <$> mapM (uncurry inferRhsWhere) rhsbinds
    qSs <- mapM (uncurry subsCheck) (zip tys' tys) -- TODO did I get this the right way around?
    qRes <- simplify (qReq ++ qDis) (concat (qsRhs ++ qSs))
    return (ve, qReq ++ qRes, qDis)

inferRhsWhere :: Rhs -> Binds -> Tc (Sigma, Q)
inferRhsWhere rhs binds = do
    ref <- newTcRef (error "inferRhsWhere: empty result")
    q <- tcRhsWhere rhs binds (Infer ref)
    ty <- readTcRef ref
    return (ty, q)


tcRhsWhere :: Rhs -> Binds -> Expected Sigma -> Tc Q
tcRhsWhere rhs binds expTy = do
  (ve, qReq, qDis) <- tcBinds binds
  extendVarEnvList ve $ do
    qRhs <- tcRhs rhs qDis expTy
    qRes <- simplify (qReq ++ qDis) qRhs
    return (qReq ++ qRes)


-- Here we'll do a hack - Rhs is *exactly* the same thing as GuardedAlts
-- when syntax is disregarded (and even then the only difference is = or ->).
-- And a rose by any other name...

rhsToGalts :: Rhs -> GuardedAlts
rhsToGalts (UnGuardedRhs e) = UnGuardedAlt e
rhsToGalts (GuardedRhss grhss) = GuardedAlts $ map grhsToGalt grhss

grhsToGalt :: GuardedRhs -> GuardedAlt
grhsToGalt (GuardedRhs l gs e) = GuardedAlt l gs e

tcRhs :: Rhs -> Q -> Expected Rho -> Tc Q
tcRhs rhs = tcGuardedAlts (rhsToGalts rhs)


-- Invariant: All PatBinds have simple PVar heads, and all
-- binders have already been gathered at an outer level
tcVarBind :: Decl -> Tc Q
tcVarBind (FunBind ms) = tcMatches ms
tcVarBind pb@(PatBind _ _ _ _ _) = do
  (_ve,qReq,_qDis) <- tcPatBinds [pb] -- qDis == []
  return qReq

tcMatches :: [Match] -> Tc Q
tcMatches ms@(Match _ n _ _ _ _ : _) = do
  ty <- lookupVar (UnQual n)
  concat <$> mapM (flip checkMatch ty) ms
  

checkMatch :: Match -> Rho -> Tc Q
checkMatch match ty = tcMatch match (Check ty)

inferMatch :: Match -> Tc (Rho, Q)
inferMatch match = do
  ref <- newTcRef $ error "inferMatch: empty result"
  q <- tcMatch match (Infer ref)
  ty <- readTcRef ref
  return (ty, q)

tcMatch :: Match -> Expected Rho -> Tc Q
tcMatch (Match _ _ ps _ rhs binds) expTy = tcAltMatch ps (rhsToGalts rhs) binds expTy
  


isExplTyped :: [Name] -> Decl -> Bool
isExplTyped ns (FunBind ms) = let Match _ n _ _ _ _ = head ms in n `elem` ns
isExplTyped ns (PatBind _ (PVar n) _ _ _) = n `elem` ns
isExplTyped _ _ = False

isImplTyped :: Decl -> Bool
isImplTyped (FunBind _) = True
isImplTyped _ = False

----------------------------------------------
--         Subsumption checking             --
----------------------------------------------

subsCheckAll :: [Sigma] -> Tc Q
subsCheckAll xs = do
  let allPairs = [ (x,y) | x <- xs, y <- xs, x /= y ]
  concat <$> mapM (uncurry subsCheck) allPairs

subsCheck :: Sigma -> Sigma -> Tc Q
subsCheck sigma1 sigma2 = do
  (skol_tvs, ctxt, rho2) <- skolemise sigma2
  q <- subsCheckRho sigma1 rho2
  qres <- simplify ctxt q
  esc_tvs <- getFreeTyVars [sigma1, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skol_tvs
  check (null bad_tvs)
        (vcat [text "Subsumption check failed:",
               nest 2 (ppr sigma1),
               text "is not as polymorphic as",
               nest 2 (ppr sigma2)])
  return qres


subsCheckRho :: Sigma -> Rho -> Tc Q

-- Rule SPEC
-- Non-empty list of var binders requires instantiation
subsCheckRho sigma1@(TcForAll (_:_) _ _) rho2 = do
  (rho1, ctxt) <- instantiate sigma1
  q <- subsCheckRho rho1 rho2
  return $ ctxt ++ q

-- Rule FUN
-- Neither argument can be a top-level Forall if we fall through here
subsCheckRho rho1 (TcTyFun a2 r2) = do
  (a1,r1) <- unifyFun rho1
  subsCheckFun a1 r1 a2 r2
subsCheckRho (TcTyFun a1 r1) rho2 = do
  (a2,r2) <- unifyFun rho2
  subsCheckFun a1 r1 a2 r2

-- Rule MONO
subsCheckRho rho1 rho2 = do
  unify rho1 rho2
  return []


subsCheckFun :: Sigma -> Rho -> Sigma -> Rho -> Tc Q
subsCheckFun a1 r1 a2 r2 = do 
  q1 <- subsCheck a2 a1
  q2 <- subsCheck r1 r2
  return $ q1 ++ q2

instSigma :: Sigma -> Expected Rho -> Tc Q
-- Invariant: if the second argument is (Check Rho),
--            then the Rho is in weak-prenex form.
instSigma t1 (Check t2) = subsCheckRho t1 t2
instSigma t1 (Infer r)  = do (t1', q) <- instantiate t1
                             writeTcRef r t1'
                             return q

instPatSigma :: Sigma -> Expected Sigma -> Tc ()
instPatSigma t1 (Check t2) = 
    do q <- subsCheck t1 t2
       -- q must be empty
       check (null q) $ (vcat [text "Pattern subsumption check failed:",
               nest 2 (ppr t1),
               text "is not as polymorphic as",
               nest 2 (ppr t2)])
instPatSigma t1 (Infer ref) = writeTcRef ref t1


--simplify :: Q -> Q -> Tc Q
--simplify _ [] = return []








module Language.Haskell.TypeCheck.Simplify where

import Language.Haskell.TypeCheck.Monad
import Language.Haskell.TypeCheck.InternalTypes

import Control.Applicative ((<$>))
import Text.PrettyPrint.HughesPJ

simplify :: TcCtxt -> TcCtxt -> Tc TcCtxt
simplify qGiven qWanted = do
  ax <- getAxioms
  axCtxts <- mapM instantiateAxiom ax
  qgs <- mapM (\a -> zonkAsst a >>= \a' -> return (a',[])) qGiven
  qWs <- zonkCtxt qWanted
--  debugShow $ show (axCtxts ++ qgs)
--  debugShow $ show qWs
  simplify' (axCtxts ++ qgs) qWs

simplify' :: [(TcAsst, TcCtxt)] -> TcCtxt -> Tc TcCtxt
simplify' env ctxt = concat <$> mapM (simplifyAsst env) ctxt

-- This is way too simplistic! 
-- Lookup can only work for "static" constraints - we need conditional unification!
simplifyAsst :: [(TcAsst, TcCtxt)] -> TcAsst -> Tc TcCtxt
simplifyAsst env asst = case lookup asst env of
                          Nothing -> return [asst] -- Not reducible
                          Just cx -> simplify' env cx

solve :: TcCtxt -> TcCtxt -> Tc ()
solve qGiven qWanted = do
  qResidual <- simplify qGiven qWanted
  check (null qResidual) $ text "Cannot solve constraints"
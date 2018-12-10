{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.PrettyPrint (
    prettifyVars
    ) where

import qualified Language.Fixpoint.Musfix.Types as MF
import qualified Data.HashMap.Strict            as M
import qualified Data.Text.Lazy                 as LT

-- | Makes variables in the output more readable
prettifyVars :: MF.MusfixInfo -> MF.MusfixInfo
prettifyVars mi = mi'
  where
    mi' = replaceSymbols symMap mi
    symMap = genSymMap mi
    
data SymGenEnv = SymGenEnv {
  nextFreeVar :: Int,
  replaceVars :: M.HashMap MF.Id MF.Id
}

-- | Maps all symbols in the Musfix info
genSymMap :: MF.MusfixInfo -> M.HashMap MF.Id MF.Id
genSymMap mi = mp
  where
    env0 = SymGenEnv { nextFreeVar = 0, replaceVars = M.empty }
    env1 = foldl fConstraints env0 $ MF.constraints mi
    env2 = foldl fWfCs env1 $ MF.wfConstraints mi
    mp = replaceVars env2
    
    -- Fold over vars
    fVar base env (MF.Var name _)
      | M.member name m     = env
      | otherwise         = env { nextFreeVar = n + 1, replaceVars = m' }
      where
        m  = replaceVars env
        n  = nextFreeVar env
        m' = M.insert name (LT.pack $ base ++ (show n)) m
            
    -- Fold over top levels
    fConstraints env (MF.HornC domain _) = foldl (fVar "v") env domain
    fWfCs env (MF.WfC _ args) = foldl (fVar "kv") env args

-- | Maps all symbols in the Musfix info
mapSymbols :: (MF.Id -> MF.Id) -> MF.MusfixInfo -> MF.MusfixInfo
mapSymbols f mi = mi'
  where
    mi' = mi { MF.qualifiers = map mQuals $ MF.qualifiers mi,
               MF.constants = map mConsts $ MF.constants mi,
               MF.distincts = map mDistincts $ MF.distincts mi,
               MF.functions = map mFuncs $ MF.functions mi,
               MF.wfConstraints = map mWfCs $ MF.wfConstraints mi,
               MF.constraints = map mConstraints $ MF.constraints mi }
    
    -- Map sorts
    mSort (MF.TypeConS name srts) = MF.TypeConS (f name) (map mSort srts)
    mSort s = s
    
    -- Map vars
    mVar (MF.Var name srt) = MF.Var (f name) (mSort srt)
    
    -- Map expressions
    mExpr (MF.SymbolExpr sym) = MF.SymbolExpr (f sym)
    mExpr (MF.AppExpr e args) = MF.AppExpr (mExpr e) (map mExpr args)
    
    -- Map top levels
    mQuals (MF.Qual name vars body) = MF.Qual (f name) (map mVar vars) (mExpr body)
    mConsts (MF.Const name srt) = MF.Const (f name) (mSort srt)
    mDistincts (MF.Distincts consts) = MF.Distincts $ map mConsts consts
    mFuncs (MF.Func name args ret) = MF.Func (f name) (map mSort args) (mSort ret)
    mWfCs (MF.WfC name args) = MF.WfC (f name) (map mVar args)
    mConstraints (MF.HornC domain expr) = MF.HornC (map mVar domain) (mExpr expr)
    
-- | Maps symbols in the Musfix info using a hash map
replaceSymbols :: M.HashMap MF.Id MF.Id -> MF.MusfixInfo -> MF.MusfixInfo
replaceSymbols m mi = mi'
  where
    mi' = mapSymbols f mi
    f sym = M.lookupDefault sym sym m
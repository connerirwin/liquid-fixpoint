{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.Translate (
    musfixInfo
    ) where

import Language.Fixpoint.Types
import Language.Fixpoint.Musfix.Util
import Data.Function
import Data.List
import qualified Language.Fixpoint.Types        as FixpointTypes
import qualified Language.Fixpoint.Musfix.Types as MF
import qualified Data.HashMap.Strict            as M
import qualified Data.Text.Lazy                 as LT

symbolId :: Symbol -> MF.Id
symbolId s = LT.fromStrict $ FixpointTypes.symbolText s

-- | Converts the given SInfo into a MusfixInfo
musfixInfo :: SInfo a -> MF.MusfixInfo
musfixInfo si = mi
  where
    mi = MF.MusfixInfo {
      MF.qualifiers = findQualifiers si,
      MF.constants = findConstants si,
      MF.distincts = findDistincts si,
      MF.functions = findFunctions si,
      MF.wfConstraints = findWfCs si,
      MF.constraints = findConstraints si
    }

-- | Gets the Musfix version of a given sort
convertSort :: Sort -> MF.Sort
convertSort FInt          = MF.IntS
convertSort (FVar n)      = MF.VarS $ LT.pack (show n)
convertSort a@(FApp _ _)  = convertAppS a
convertSort (FTC f)       = MF.TypeConS (symbolId (symbol f)) []
convertSort (FAbs _ s)    = convertSort s
convertSort _             = error "unsupported sort"

convertAppS :: Sort -> MF.Sort
convertAppS s = MF.TypeConS name args
  where
    name = rootc s
    args = collect s []
    
    rootc (FApp a _) = rootc a
    rootc (FTC f)    = symbolId $ symbol f
    rootc (FVar n)   = LT.pack $ "@tycon" ++ (show n)
    rootc _          = error "application in sort has no leftmost type constructor"
    
    collect (FApp a b) ts = args
      where
        args  = collect a (rarg:ts)
        rarg  = convertSort b
    collect _ ts     = ts

-- | Converts the given function sort into a Musfix function signature
convertFuncSort :: Sort -> ([MF.Sort], MF.Sort)
convertFuncSort f@(FFunc _ _) = (map convertSort $ formals f, convertSort $ ret f)
  where
    formals (FFunc a r) = a:(formals r)
    formals _           = []
    
    ret (FFunc _ r) = ret r
    ret s           = s
convertFuncSort (FAbs _ p)    = convertFuncSort p
convertFuncSort _             = error "not a function sort"

-- | Converts the given binary operator
convertBop :: Bop -> MF.Expr
convertBop op = MF.SymbolExpr s
  where
    s = case op of
      Plus    -> "+"
      Minus   -> "-"
      Times   -> "*"
      Div     -> "/"
      RTimes  -> "*"
      RDiv    -> "/"
      Mod     -> "mod"
      
      
-- | Converts the given binary relation
convertBrel :: Brel -> MF.Expr
convertBrel rel = MF.SymbolExpr s
  where
    s = case rel of
      Eq      -> "="
      Ueq     -> "="
      Gt      -> ">"
      Ge      -> ">="
      Lt      -> "<"
      Le      -> "<="
      _       -> "unknown_binary_relation"

convertSymConst :: SymConst -> MF.Expr
convertSymConst (SL t)       = MF.SymbolExpr $ LT.fromStrict t

convertConst :: Constant -> MF.Expr
convertConst    (I i)        = MF.SymbolExpr $ LT.pack (show i)
convertConst    (R d)        = MF.SymbolExpr $ LT.pack (show d)
convertConst    (L t _)      = MF.SymbolExpr $ LT.pack (show t)

-- | Converts the given expression into a (simplified) Musfix expression
convertExpr :: Expr -> MF.Expr
convertExpr (ESym s)          = convertSymConst s
convertExpr (ECon s)          = convertConst s -- TODO: Use this to identify constants? Or is this something else?
convertExpr (EVar s)          = MF.SymbolExpr $ symbolId s
convertExpr e@(EApp _ _)      = convertAppExpr e -- needs to unwrap currying
convertExpr (ENeg e)          = MF.AppExpr (MF.SymbolExpr "-") [convertExpr e]
convertExpr (EBin o l r)      = MF.AppExpr (convertBop o) [convertExpr l, convertExpr r]
convertExpr (EIte c t e)      = MF.AppExpr (MF.SymbolExpr "ite") [convertExpr c, convertExpr t, convertExpr e]
convertExpr (ECst e _ )       = convertExpr e
convertExpr PTrue             = MF.SymbolExpr "True"
convertExpr PFalse            = MF.SymbolExpr "False"
convertExpr (PAnd [])         = convertExpr PTrue
convertExpr (PAnd es)         = MF.AppExpr (MF.SymbolExpr "and") $ map convertExpr es
convertExpr (POr [])          = convertExpr PFalse
convertExpr (POr es)          = MF.AppExpr (MF.SymbolExpr "or") $ map convertExpr es
convertExpr (PNot e)          = MF.AppExpr (MF.SymbolExpr "not") [convertExpr e]
convertExpr (PImp p q)        = MF.AppExpr (MF.SymbolExpr "=>") [convertExpr p, convertExpr q]
convertExpr (PIff p q)        = MF.AppExpr (MF.SymbolExpr "=") [convertExpr p, convertExpr q]
convertExpr (PKVar k s)       = convertKVar k s
convertExpr (PAtom r e1 e2)   = convertRel r e1 e2
convertExpr _                 = error "unsupported expression"

convertAppExpr :: Expr -> MF.Expr
convertAppExpr e = MF.AppExpr rootExpr args
  where
    rootExpr = rootc e
    args = collect e []
    
    rootc (EApp a _) = rootc a
    rootc (EVar s)   = MF.SymbolExpr $ symbolId s
    rootc (ECst e _) = rootc e
    rootc _          = error "application in expression has no compatible leftmost expression"
    
    collect (EApp a b) ts = args
      where
        args  = collect a (rarg:ts)
        rarg  = convertExpr b
    collect (ECst e _ ) ts = collect e ts
    collect _ ts     = ts

convertKVar :: KVar -> Subst -> MF.Expr
convertKVar k subst = MF.AppExpr (MF.SymbolExpr $ symbolId (kv k)) args
  where
    (Su m) = subst
    argSort = sortBy (compare `on` fst)
    args = map (convertExpr . snd) (argSort (M.toList m))
    
convertRel :: Brel -> Expr -> Expr -> MF.Expr
convertRel Ne  e1 e2 = convertNe e1 e2
convertRel Une e1 e2 = convertNe e1 e2
convertRel r   e1 e2 = MF.AppExpr (convertBrel r) [(convertExpr e1), (convertExpr e2)]

convertNe :: Expr -> Expr -> MF.Expr
convertNe e1 e2      = MF.AppExpr (MF.SymbolExpr "not") [MF.AppExpr (MF.SymbolExpr "=") [convertExpr e1, convertExpr e2]]

-- | Finds constants in the given SInfo
findConstants :: SInfo a -> [MF.Const]
findConstants si = map box constLits
  where
    globalLits = toListSEnv $ gLits si
    constLits  = constantLiterals globalLits
    
    box (sym, srt) = MF.Const (symbolId sym) (convertSort srt)
    
-- | Find distinct constants in the given SInfo
findDistincts :: SInfo a -> [MF.Distincts]
findDistincts si = map box distinctLits
  where
    distinctLits = groupBySorts $ toListSEnv (dLits si)
    
    box (srt, names) = MF.Distincts $ map boxC names
      where
        boxC name = MF.Const (symbolId name) (convertSort srt)
    
-- | Finds uninterpreted functions in the given SInfo
findFunctions :: SInfo a -> [MF.Func]
findFunctions si = map box funcLits
  where
    globalLits = toListSEnv $ gLits si
    funcLits   = functionLiterals globalLits
    
    box (sym, srt) = MF.Func (symbolId sym) args ret
      where
        (args, ret) = convertFuncSort srt
        
-- | Finds all qualifiers in the given SInfo
findQualifiers :: SInfo a -> [MF.Qual]
findQualifiers si = map boxQ qs
  where
    qs = quals si
    
    boxQ q = MF.Qual (symbolId $ qName q) (map boxP $ qParams q) (convertExpr $ qBody q)
    boxP p = MF.Var (symbolId $ qpSym p) (convertSort $ qpSort p)
    
-- | Finds all WfC in the given SInfo
findWfCs :: SInfo a -> [MF.WfC]
findWfCs si = map box wfcs
  where
    wfcs = M.toList (ws si)
    
    box (k, wf) = MF.WfC name $ map svar domain
      where
        name        = LT.append "$" (symbolId . kv $ k)
        fmlSort     = sortBy (compare `on` fst)
        domain      = fmlSort $ sortedDomainWfC (bs si) wf
        svar (n, s) = MF.Var (symbolId n) (convertSort s)
        
-- | Finds all the horn constraints in the given SInfo
findConstraints :: SInfo a -> [MF.HornC]
findConstraints si = map box constraints
  where
    constraints = M.toList (cm si)
    
    box (_, c) = MF.HornC vars $ MF.AppExpr (MF.SymbolExpr "=>") [lhs, rhs]
      where
        lhs       = combinedRefts lhsRefts
        rhs       = convertExpr $ crhs c
        
        binds     = bs si
        lhsRefts  = clhs binds c
        domain    = (sortedDomainSimpC binds c)
        
        vars      = map sortedVar (filter isNotGlobalDef domain)
        
        isNotGlobalDef (s, _) = not $ hasGlobalDef si s
        sortedVar (s, srt) = MF.Var (symbolId s) (convertSort srt)
        combinedRefts xs = convertExpr $ filterRedundantBools eAnds
          where
            eAnds = PAnd $ map expr xs
            expr :: (Symbol, SortedReft) -> Expr
            expr (s, sreft) = e'
              where
                Reft (_, e) = sr_reft sreft
                e' = (renameVar "v" s) e

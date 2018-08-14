{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.Util where
  
import Language.Fixpoint.Types

import Data.Semigroup
import Data.Text.Format
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy as LT

-- | Turns a list of builders into one concatenated sequence
concatBuilders :: [Builder] -> Builder
concatBuilders bs = foldl (<>) "" bs

-- | Concatenates builders with a given separator
concatBuildersS :: LT.Text -> [Builder] -> Builder
concatBuildersS _ []      = ""
concatBuildersS _ [b]     = b
concatBuildersS s (b:bs)  = build "{}{}{}" (b, s, concatBuildersS s bs)

-- | Gets the sorted domain of a WfC constraint
sortedDomain :: BindEnv -> WfC a -> [(Symbol, Sort)]
sortedDomain env wf = (vName, vSort) : map symSorts (envCs env $ wenv wf)
  where
    (vName, vSort, _) = wrft wf
    symSorts (sym, sreft) = (sym, sr_sort sreft)
    
-- | Renames all occurances of the given variable
renameVar :: String -> Symbol -> Expr -> Expr
renameVar s s' e = rv e
  where
    rv (EVar n)
      | symbolString n == s = EVar s'
    rv (EApp f a)           = EApp (rv f) (rv a)
    rv (ENeg e)             = ENeg $ rv e
    rv (EBin o l r)         = EBin o (rv l) (rv r)
    rv (EIte c t e)         = EIte (rv c) (rv t) (rv e)
    rv (ECst p x)           = ECst (rv p) x
    rv (PAnd xs)            = PAnd $ map rv xs
    rv (POr  xs)            = POr $ map rv xs
    rv (PNot e)             = PNot $ rv e
    rv (PImp p q)           = PImp (rv p) (rv q)
    rv (PIff p q)           = PIff (rv p) (rv q)
    rv (PAtom r e1 e2)      = PAtom r (rv e1) (rv e2)
    rv e                    = e
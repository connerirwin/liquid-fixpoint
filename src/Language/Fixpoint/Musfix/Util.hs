{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.Util where

import Language.Fixpoint.Types
import Language.Fixpoint.Types.Visitor

import Data.Semigroup
import Data.Text.Format
import Data.Text.Lazy.Builder (Builder)
import qualified Data.HashMap.Strict    as M
import qualified Data.Text.Lazy as LT

-- | TODO Prune unnecessary qualifiers and such
ignoredFuncs :: [String]
ignoredFuncs = ["Set_sng"]

-- | Gets whether or not the given sort is a function sort
isFunctionSort :: Sort -> Bool
isFunctionSort (FFunc _ _) = True
isFunctionSort (FAbs  _ s) = isFunctionSort s
isFunctionSort _           = False

-- | Gets all the functions from a list of symbols and their sorts
functionLiterals :: [(Symbol, Sort)] -> [(Symbol, Sort)]
functionLiterals xs = filter (\x -> isFunctionSort (snd x) && g x) xs
  where
    g (sym, _) = not $ (symbolString sym) `elem` ignoredFuncs

-- | Gets all the constants from a list of symbols and their sorts
constantLiterals :: [(Symbol, Sort)] -> [(Symbol, Sort)]
constantLiterals xs = filter (not . isFunctionSort . snd) xs

-- | Whether or not the symbol has a global definition
hasGlobalDef :: SInfo a -> Symbol -> Bool
hasGlobalDef si sym = memberSEnv sym (gLits si)

-- | Groups symbols by their sort
groupBySorts :: [(Symbol, Sort)] -> [(Sort, [Symbol])]
groupBySorts xs = M.toList $ toMap xs M.empty
  where
    toMap :: [(Symbol, Sort)] -> M.HashMap Sort [Symbol] -> M.HashMap Sort [Symbol]
    toMap ((sym, srt):xs) mp = toMap xs (M.alter f srt mp)
      where
        f (Just syms) = Just $ syms ++ [sym]
        f Nothing     = Just $ [sym]
    toMap _ mp      = mp

-- | Turns a list of builders into one concatenated sequence
concatBuilders :: [Builder] -> Builder
concatBuilders bs = foldl (<>) "" bs

-- | Concatenates builders with a given separator
concatBuildersS :: LT.Text -> [Builder] -> Builder
concatBuildersS _ []      = ""
concatBuildersS _ [b]     = b
concatBuildersS s (b:bs)  = build "{}{}{}" (b, s, concatBuildersS s bs)

-- | Gets the sorted domain of a WfC constraint
sortedDomainWfC :: BindEnv -> WfC a -> [(Symbol, Sort)]
sortedDomainWfC env wf = (vName, vSort) : map symSorts (envCs env $ wenv wf)
  where
    (vName, vSort, _) = wrft wf
    symSorts (sym, sreft) = (sym, sr_sort sreft)
    
-- | Gets the sorted domain of a Horn constraint
sortedDomainSimpC :: BindEnv -> SimpC a -> [(Symbol, Sort)]
sortedDomainSimpC binds c = lhsVars ++ rhsVars
  where
    lhsVars = map srVar $ clhs binds c
    rhsVars = []
    
    srVar (sym, sreft) = (sym, sr_sort sreft)
    
-- | Gets all variable symbols in an expression
{--exprVars :: Expr -> [Symbol]
exprVars e = M.keys $ f M.empty e
  where
    f :: M.HashMap Symbol Bool -> Expr -> M.HashMap Symbol Bool
    f m (EVar s)        = M.insert s True m
    f m (EApp a b)      = M.union (f m a) (f m b)
    f m (ENeg a)        = f m a
    f m (EBin _ l r)    = M.union (f m l) (f m r)
    f m (EIte c t e)    = foldl M.union (f m c) [(f m t), (f m e)]
    f m (ECst p _)      = f m p
    f m (PAnd ps)       = foldl M.union $ map (f m) ps
    f m (POr  ps)       = foldl M.union $ map (f m) ps
    f m (PNot a)        = f m a
    f m (PImp p q)      = M.union (f m p) (f m q)
    f m (PIff p q)      = M.union (f m p) (f m q)
    f m _               = m
    --}

-- | Filters out redudant booleans in AND/OR expressions
filterRedundantBools :: Expr -> Expr
filterRedundantBools e      = mapExpr f e
  where
    f (PAnd xs)
      | length xs' > 1      = PAnd xs'
      | length xs == 0      = PTrue
      | otherwise           = head xs
      where
        xs' = filter notTrue xs
        notTrue PTrue = False
        notTrue _     = True
    f (POr xs)
      | length xs' > 1      = POr xs'
      | length xs == 0      = PFalse
      | otherwise           = head xs
      where
        xs' = filter notFalse xs
        notFalse PFalse     = False
        notFalse _          = True
    f e                     = e

-- | Renames all occurances of the given variable
renameVar :: String -> Symbol -> Expr -> Expr
renameVar s s' e = mapExpr rv e
  where
    rv (EVar n)
      | symbolString n == s = EVar s'
    rv e                    = e

-- | Gets the name of a sort type constructor with respect to the number of arguments given
appSortName :: Sort -> Maybe (Symbol, Int)
appSortName s = sname 0 s
  where
    sname d (FApp a _) = sname (d + 1) a
    sname d (FTC a) 
      | s `elem` prims = Nothing
      | otherwise      = Just ((symbol a), d)
      where
        s = symbolString $ symbol a
        prims = [ "Int", "Bool" ]
    sname _ _ = Nothing    

-- | Gets all uninterpreted sort constructors in a given sort
constructorsInSort :: Sort -> [(Symbol, Int)]
constructorsInSort = find
  where
    find (FFunc a b)              = (find a) ++ (find b)
    find f@(FApp _ b)
      | Just fnd <- appSortName f = fnd:(find b)
    find (FAbs _ s)               = find s
    find f@(FTC _)
      | Just fnd <- appSortName f = [fnd]
    find _                        = []

-- | Gets all uninterpreted sorts from uninterpreted functions
uninterpretedSorts :: SInfo a -> [(Symbol, [Int])]
uninterpretedSorts si = M.toList symMap
  where
    symMap = foldl collect M.empty fromLiterals
    
    -- Sorts from literals
    gBinds = toListSEnv $ gLits si
    fromLiterals = foldl (++) [] (map (constructorsInSort . snd) gBinds)
    
    -- Sorts from expressions
    
    -- Collect sorts into a hash map (deduplicating)
    collect :: M.HashMap Symbol [Int] -> (Symbol, Int) -> M.HashMap Symbol [Int]
    collect m (name, num) = M.insert name counts' m
      where
        counts = M.lookupDefault [] name m
        counts' = if num `elem` counts then counts else num:counts

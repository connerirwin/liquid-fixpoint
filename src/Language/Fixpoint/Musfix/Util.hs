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

-- |
data LiteralType =
    FunctionLiteral
  | ConstantLiteral
  deriving (Enum)

-- | Gets the type of a given literal from a sort
literalType :: Sort -> LiteralType
literalType (FFunc _ _) = FunctionLiteral
literalType (FAbs  _ s) = literalType s
literalType _           = ConstantLiteral

functionLiterals :: [(Symbol, Sort)] -> [(Symbol, Sort)]
functionLiterals xs = filter (\x -> f' x && g x) xs
  where
    f' (_, s) = case literalType s of
        FunctionLiteral -> True
        _               -> False

    g (sym, _) = not $ (symbolString sym) `elem` ignoredFuncs

constantLiterals :: [(Symbol, Sort)] -> [(Symbol, Sort)]
constantLiterals xs = filter f' xs
  where
    f' (_, s) = case literalType s of
        ConstantLiteral -> True
        _               -> False

-- | True if the symbol is included in a global definition 
hasGlobalDef :: SInfo a -> Symbol -> Bool
hasGlobalDef si sym = memberSEnv sym (gLits si)

-- | Get the formal types of a function sort
formalSortsFuncS :: Sort -> [Sort]
formalSortsFuncS (FFunc a r) = a:(formalSortsFuncS r)
formalSortsFuncS _           = []

-- | Get the return type of a function sort
returnSortFuncS :: Sort -> Sort
returnSortFuncS (FFunc _ r) = returnSortFuncS r
returnSortFuncS s           = s

-- | Groups symbols by their sort
groupBySorts :: [(Symbol, Sort)] -> [[Symbol]]
groupBySorts xs = M.elems $ toMap xs M.empty
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
sortedDomain :: BindEnv -> WfC a -> [(Symbol, Sort)]
sortedDomain env wf = (vName, vSort) : map symSorts (envCs env $ wenv wf)
  where
    (vName, vSort, _) = wrft wf
    symSorts (sym, sreft) = (sym, sr_sort sreft)

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

data UninterpSort = UninterpSort Symbol Int

-- | Gets all uninterpreted sort constructors in a given sort
constructorsInSort :: Sort -> [UninterpSort]
constructorsInSort = find
  where
    find (FFunc a b)  = (find a) ++ (find b)
    find f@(FApp _ b)
      | Just fnd <- appSortName f = fnd:(find b)
    find (FAbs _ s)   = find s
    find f@(FTC _)
      | Just fnd <- appSortName f = [fnd]
    find _            = []

-- | Gets all uninterpreted sorts from uninterpreted functions
uninterpretedSorts :: SInfo a -> [(Symbol, [Int])]
uninterpretedSorts si = M.toList symMap
  where
    symMap = foldl collect M.empty cons
    gBinds = toListSEnv $ gLits si
    lits = functionLiterals gBinds
    cons = foldl (++) [] (map (constructorsInSort . snd) lits)
    collect :: M.HashMap Symbol [Int] -> UninterpSort -> M.HashMap Symbol [Int]
    collect m (UninterpSort name num) = M.insert name counts' m
      where
        counts = M.lookupDefault [] name m
        counts' = if num `elem` counts then counts else num:counts
    
appSortName :: Sort -> Maybe UninterpSort
appSortName s = sname 0 s
  where
    sname d (FApp a _) = sname (d + 1) a
    sname d (FTC a) = Just $ UninterpSort (symbol a) d
    sname _ _ = Nothing

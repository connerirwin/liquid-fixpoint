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
import qualified Data.Char                      as C

symbolId :: Symbol -> MF.Id
symbolId s = LT.fromStrict $ FixpointTypes.symbolText s

-- | Converts the given SInfo into a MusfixInfo
musfixInfo :: SInfo a -> MF.MusfixInfo
musfixInfo si = mi'
  where
    mi' = ( replaceEmptySets .
            removeRedundantBools .
            removeUnusedReferences .
            escapeVars .
            filterBuiltInSorts .
            removeApplyApps . 
            escapeGlobals . 
            renameConstructorFuncs .
            addUninterpSorts . 
            (replaceSymbols primitiveTranslations)) mi
    mi = MF.MusfixInfo {
      MF.qualifiers = findQualifiers si,
      MF.constants = findConstants si,
      MF.distincts = findDistincts si,
      MF.functions = findFunctions si,
      MF.wfConstraints = findWfCs si,
      MF.constraints = findConstraints si,
      MF.sorts = [] -- these must be found
    }
    
-- | Translations to specific Musfix types/symbols
primitiveTranslations :: M.HashMap MF.Id MF.Id
primitiveTranslations = M.fromList [ 
                                ("Set_cup",        "union")
                              , ("Set_cap",    "intersect")
                              , ("Set_Set",          "Set")
                              , ("Set_sng",          "Set")
                              , ("Set_mem",           "in")
                              , ("bool",            "Bool")
                              , ("GHC.Types.Bool",  "Bool")
                              , ("[]",              "List")
                              ]
                              
builtInSorts :: [MF.Id]
builtInSorts = [ "Bool", "Int", "Set" ]
    
-- | Gets the Musfix version of a given sort
convertSort :: Sort -> MF.Sort
convertSort FInt          = MF.IntS
convertSort (FVar n)      = MF.VarS $ LT.pack (show n)
convertSort (FObj s)      = MF.TypeConS (LT.append "Obj_" $ symbolId s) []
convertSort a@(FApp _ _)  = convertAppS a
convertSort (FTC f)       = MF.TypeConS (symbolId (symbol f)) []
convertSort (FAbs _ s)    = convertSort s
convertSort (FFunc _ _)   = error "unexpected function sort"
convertSort _             = error "unsupported sort"

convertAppS :: Sort -> MF.Sort
convertAppS s = MF.TypeConS name args
  where
    name = rootc s
    args = collect s []
    
    rootc (FApp a _) = rootc a
    rootc (FTC f)    = symbolId $ symbol f
    rootc (FVar n)   = LT.pack $ "@t" ++ (show n)
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
convertExpr (PAnd es)         = convertAndOr "and" es
convertExpr (POr [])          = convertExpr PFalse
convertExpr (POr es)          = convertAndOr "or" es
convertExpr (PNot e)          = MF.AppExpr (MF.SymbolExpr "not") [convertExpr e]
convertExpr (PImp p q)        = MF.AppExpr (MF.SymbolExpr "=>") [convertExpr p, convertExpr q]
convertExpr (PIff p q)        = MF.AppExpr (MF.SymbolExpr "=") [convertExpr p, convertExpr q]
convertExpr (PKVar k s)       = convertKVar k s
convertExpr (PAtom r e1 e2)   = convertRel r e1 e2
convertExpr _                 = error "unsupported expression"

convertAndOr :: MF.Id -> [Expr] -> MF.Expr
convertAndOr _  [a] = convertExpr a
convertAndOr op (a:b:xs) = MF.AppExpr (MF.SymbolExpr op) [convertExpr a, convertAndOr op (b:xs)]
convertAndOr op _ = MF.AppExpr (MF.SymbolExpr "empty") [MF.SymbolExpr op]

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
convertKVar k subst = MF.AppExpr (MF.SymbolExpr $ name) args
  where
    name = LT.append "$" (symbolId (kv k))
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
        combinedRefts xs = convertExpr eAnds
          where
            eAnds = PAnd $ map expr xs
            expr :: (Symbol, SortedReft) -> Expr
            expr (s, sreft) = e'
              where
                Reft (_, e) = sr_reft sreft
                e' = (renameVar "v" s) e

-- | Adds uninterpreted sorts to the Musfix info based on contextual usage of what appear to be type constructors               
addUninterpSorts :: MF.MusfixInfo -> MF.MusfixInfo
addUninterpSorts mi = mi2
  where
    mi1 = mi {
        MF.sorts = foldr dec [] $ M.toList fnd5
      }
    mi2 = disambiguateTypeCons fnd5 mi1
    
    gls = globals mi
    
    fnd1 = foldl searchConstants M.empty (MF.constants mi)
    fnd2 = foldl searchFunctions fnd1 (MF.functions mi)
    fnd3 = foldl searchQualifiers fnd2 (MF.qualifiers mi)
    fnd4 = foldl searchWfCs fnd3 (MF.wfConstraints mi)
    fnd5 = foldl searchConstraints fnd4 (MF.constraints mi)
    
    -- currently expressions aren't searched, but so far nothing has come up 
    -- as a constructor without a corresponding sort declaration elsewhere
    
    dec :: (MF.Id, [Int]) -> [MF.SortDecl] -> [MF.SortDecl]
    dec (name, nums) decls = foldr ((:) . d) decls nums
      where
        d n
          | length nums > 1   = MF.SortDecl (LT.append name (LT.pack $ show n)) n
          | otherwise         = MF.SortDecl name n
    
    insertUnique k v m
      | M.member k gls  = m
      | v `elem` nums   = m
      | otherwise       = M.insert k (v:nums) m
      where
        nums = M.lookupDefault [] k m
    
    searchSort m (MF.TypeConS name srts) = m2
      where
        m1 = foldl searchSort m srts
        m2 = case LT.head name of
          '@' -> m1
          _   -> insertUnique name (length srts) m1
    searchSort m _ = m
    
    searchVar m (MF.Var _ srt) = searchSort m srt
        
    searchConstants m (MF.Const _ srt) = searchSort m srt
    searchFunctions m (MF.Func _ args ret) = m2
      where
        m1 = foldl searchSort m args
        m2 = searchSort m1 ret
    searchQualifiers m (MF.Qual _ vars _) = foldl searchVar m vars
    searchWfCs m (MF.WfC _ args) = foldl searchVar m args
    searchConstraints m (MF.HornC domain _) = foldl searchVar m domain
    
-- | Disambiguates type constructors that take variable arguments
disambiguateTypeCons :: M.HashMap MF.Id [Int] -> MF.MusfixInfo -> MF.MusfixInfo
disambiguateTypeCons ms mi = mi'
  where
    mi' = mi { MF.qualifiers = map mQuals $ MF.qualifiers mi,
               MF.constants = map mConsts $ MF.constants mi,
               MF.functions = map mFuncs $ MF.functions mi,
               MF.wfConstraints = map mWfCs $ MF.wfConstraints mi,
               MF.constraints = map mConstraints $ MF.constraints mi }
               
    nd name = (length nums > 1)
      where
        nums = M.lookupDefault [] name ms
    
    mSort (MF.TypeConS name srt) = MF.TypeConS name' (map mSort srt)
      where
        name' = if nd name then 
            LT.append name (LT.pack $ show (length srt))
          else 
            name
    mSort s = s
    mVar (MF.Var name sort) = MF.Var name (mSort sort)
    mQuals (MF.Qual name vars expr) = MF.Qual name (map mVar vars) (mExpr expr)
    mConsts (MF.Const name srt) = MF.Const name (mSort srt)
    mFuncs (MF.Func name args ret) = MF.Func name (map mSort args) (mSort ret)
    mWfCs (MF.WfC name vars) = MF.WfC name (map mVar vars)
    mConstraints (MF.HornC domain expr) = MF.HornC (map mVar domain) (mExpr expr)
    mExpr (MF.AppExpr (MF.SymbolExpr f) as)
      | nd f = MF.AppExpr (MF.SymbolExpr f') (map mExpr as)
      where
        f' = LT.append f (LT.pack $ show (length as))
    mExpr (MF.AppExpr f as) = MF.AppExpr (mExpr f) (map mExpr as)
    mExpr e = e
    
-- | Gets a hashmap of all the globals in the Musfix info
globals :: MF.MusfixInfo -> M.HashMap MF.Id Bool
globals mi = gls3
  where
    gls1 = foldl inclConsts M.empty (MF.constants mi)
    gls2 = foldl inclFuncs gls1 (MF.functions mi)
    gls3 = foldl inclSorts gls2 (MF.sorts mi)
    
    inclConsts m (MF.Const name _) = M.insert name True m
    inclFuncs m (MF.Func name _ _) = M.insert name True m
    inclSorts m (MF.SortDecl name _) = M.insert name True m
                
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
    
-- | Removes apply's from function applications
-- | Currently apply's are filtered out, but it would be realitively easier to create a transformation that keeps them and replaces all functions with integer constants
removeApplyApps :: MF.MusfixInfo -> MF.MusfixInfo
removeApplyApps mi = mi1
  where
    mi1 = mi {
      MF.constraints = map rmC $ MF.constraints mi
    }
    
    rmC (MF.HornC domain expr) = MF.HornC domain $ rmE expr
    
    rmE (MF.AppExpr (MF.SymbolExpr "apply") (a:as)) = MF.AppExpr (rmE a) (map rmE as)
    rmE (MF.AppExpr e as) = MF.AppExpr (rmE e) (map rmE as)
    rmE e = e
    
-- | Filters built in sorts
filterBuiltInSorts :: MF.MusfixInfo -> MF.MusfixInfo
filterBuiltInSorts mi = mi'
  where
    mi' = mi { MF.sorts = filter nbi $ MF.sorts mi }
    nbi (MF.SortDecl name _)
      | name `elem` builtInSorts  = False
      | otherwise                 = True
      
-- | Fixes weird constructors that have the same name as their return sort
renameConstructorFuncs :: MF.MusfixInfo -> MF.MusfixInfo
renameConstructorFuncs mi = mi'
  where
    mi' = mi {
      MF.functions = map (renameF cfs) $ MF.functions mi,
      MF.qualifiers = map (renameQ cfs) $ MF.qualifiers mi,
      MF.constraints = map (renameC cfs) $ MF.constraints mi
    }
    
    cfs = foldl findCFs M.empty $ MF.functions mi
    
    findCFs m f@(MF.Func name _ _)
      | isCF f    = M.insert name name' m
      | otherwise = m
      where
        name' = LT.append "_mk_" name
      
    isCF (MF.Func name _ ret) = case ret of
        (MF.TypeConS n srts) -> (length srts == 0) && name == n
        _ -> False
        
    renameE m (MF.AppExpr (MF.SymbolExpr name) as) = MF.AppExpr (MF.SymbolExpr name') (map (renameE m) as)
      where
        name' = if length as > 0 then
            M.lookupDefault name name m
          else
            name
    renameE m (MF.AppExpr f as) = MF.AppExpr (renameE m f) (map (renameE m) as)
    renameE _ e = e
    
    renameF m (MF.Func name args ret) = MF.Func name' args ret
      where
        name' = M.lookupDefault name name m
        
    renameQ m (MF.Qual name vars e) = MF.Qual name vars (renameE m e)
    renameC m (MF.HornC vars e) = MF.HornC vars (renameE m e)
    
-- | Escapes all known global symbols
escapeGlobals :: MF.MusfixInfo -> MF.MusfixInfo
escapeGlobals mi = mi'
  where
    mi' = replaceSymbols mp2 mi
    
    mp1 = foldl escConsts M.empty (MF.constants mi)
    mp2 = foldl escFuncs mp1 (MF.functions mi)
    
    mapIfUpper m name
      | isUpper           = M.insert name safe m
      | otherwise         = m
      where
        isUpper           = C.isUpper $ LT.head name
        safe              = LT.cons '_' name
    
    escConsts m (MF.Const name _) = mapIfUpper m name
    escFuncs m (MF.Func name _ _) = mapIfUpper m name

-- | Escapes variable names
escapeVars :: MF.MusfixInfo -> MF.MusfixInfo
escapeVars mi = mi'
  where
    mi' = mi { MF.qualifiers = map mQuals $ MF.qualifiers mi,
               MF.wfConstraints = map mWfCs $ MF.wfConstraints mi,
               MF.constraints = map mConstraints $ MF.constraints mi }
    
    -- Map vars
    mapIfUpper m (MF.Var name _)
      | isUpper           = M.insert name safe m
      | otherwise         = m
      where
        isUpper           = C.isUpper $ LT.head name
        safe              = LT.cons '_' name
    
    -- Map expressions
    replaceVarsE m (MF.SymbolExpr sym) = MF.SymbolExpr (M.lookupDefault sym sym m)
    replaceVarsE m (MF.AppExpr e args) = MF.AppExpr (replaceVarsE m e) (map (replaceVarsE m) args)
    
    replaceVarsV m (MF.Var name srt) = MF.Var (M.lookupDefault name name m) srt
    
    -- Map top levels
    mQuals (MF.Qual name vars body) = MF.Qual name vars' body'
      where
        replacements = foldl mapIfUpper M.empty vars
        vars' = map (replaceVarsV replacements) vars
        body' = replaceVarsE replacements body
        
    mWfCs (MF.WfC name args) = MF.WfC name args'
      where
        replacements = foldl mapIfUpper M.empty args
        args' = map (replaceVarsV replacements) args
        
    mConstraints (MF.HornC domain expr) = MF.HornC domain' expr'
      where
        replacements = foldl mapIfUpper M.empty domain
        domain' = map (replaceVarsV replacements) domain
        expr' = replaceVarsE replacements expr

-- | Removes objects that are defined but not used
-- Currently this is limited to horn constraint domains.
removeUnusedReferences :: MF.MusfixInfo -> MF.MusfixInfo
removeUnusedReferences mi = mi'
  where
    mi' = mi { MF.constraints = map mConstraints $ MF.constraints mi }
    
    mConstraints (MF.HornC domain expr) = MF.HornC domain' expr
      where
        domain' = filter (refsVar expr) domain
        
    refsVar e (MF.Var name _) = hasSym name e
    
    hasSym :: MF.Id -> MF.Expr -> Bool
    hasSym sym (MF.SymbolExpr s) = (s == sym)
    hasSym sym (MF.AppExpr e args) = foldl f False (e:args)
      where
        f r e = r || (hasSym sym e)
        
-- | Removes redundant booleans in and/or expressions
removeRedundantBools :: MF.MusfixInfo -> MF.MusfixInfo
removeRedundantBools mi = mi'
  where
    mi' = mi {
      MF.qualifiers = map mQuals $ MF.qualifiers mi,
      MF.constraints = map mConstraints $ MF.constraints mi
    }
    
    mExpr (MF.AppExpr (MF.SymbolExpr "and") [e1, e2])
      | e1 == (MF.SymbolExpr "True")  = mExpr e2
      | e2 == (MF.SymbolExpr "True")  = mExpr e1
    mExpr (MF.AppExpr (MF.SymbolExpr "or") [e1, e2])
      | e1 == (MF.SymbolExpr "False") = mExpr e2
      | e2 == (MF.SymbolExpr "False") = mExpr e1
    mExpr (MF.AppExpr e args)         = MF.AppExpr (mExpr e) (map mExpr args)
    mExpr e                           = e
    
    mQuals (MF.Qual name vars body) = MF.Qual name vars $ mExpr body
    mConstraints (MF.HornC domain expr) = MF.HornC domain $ mExpr expr
    
-- | Replaces empty set constructors with literals
replaceEmptySets :: MF.MusfixInfo -> MF.MusfixInfo
replaceEmptySets mi = mi'
  where
    mi' = mi {
      MF.qualifiers = map mQuals $ MF.qualifiers mi,
      MF.constraints = map mConstraints $ MF.constraints mi
    }
    
    mExpr (MF.AppExpr (MF.SymbolExpr "Set_empty") _) = MF.SymbolExpr "{}"
    mExpr (MF.AppExpr e args)         = MF.AppExpr (mExpr e) (map mExpr args)
    mExpr e                           = e
    
    mQuals (MF.Qual name vars body) = MF.Qual name vars $ mExpr body
    mConstraints (MF.HornC domain expr) = MF.HornC domain $ mExpr expr

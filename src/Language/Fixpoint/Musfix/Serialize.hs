{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.Serialize (
    musfix
  , musfixFromInfo
  , convertToMusFix
  ) where

import Language.Fixpoint.Types
import Language.Fixpoint.Musfix.Util

import Data.Function
import Data.List
import Data.Text.Format
import Data.Text.Lazy.Builder (Builder)
import qualified Data.HashMap.Strict    as M
import qualified Data.Text.Lazy         as LT
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.List              as L

import Debug.Trace

-- | Default pretty names
nameTranslations :: M.HashMap String String
nameTranslations = M.fromList [ ("Set_cup",     "union")
                              , ("Set_cap", "intersect")
                              , ("Set_Set",       "Set")
                              , ("Set_sng",       "Set")
                              , ("Set_mem",        "in")
                              , ("bool",         "Bool")
                              ]

-- | Converts the given SInfo object into a MUSFix compatible string
convertToMusFix :: SInfo a -> String
convertToMusFix si = (LT.unpack (Builder.toLazyText (musfixFromInfo si)))

-- | Produce a lazy-text builder from the given SInfo
musfixFromInfo :: SInfo a -> Builder
musfixFromInfo si = build txt (decList, decSorts, decConsts, decDists, decFuncs, qualifiers, wfcs, horns)
    where
      env = ConvertEnv {
              ceSInfo = si,
              cePrettyVars = nameTranslations
            }
      gBinds = toListSEnv $ gLits si
      txt = "; Uninterpreted Sorts\n{}\n{}\n\n; Constants\n{}\n\n; Distinct Constants\n{}\n\n; Uninterpreted Functions\n{}\n\n; Qualifiers\n{}\n\n; Well-formedness Constraints\n{}\n\n; Horn Constraints\n{}"
      decList :: String
      decList     = "(declare-sort List 1)"
      decSorts    = concatBuilders $ map (musfix env) (ddecls si)
      decConsts   = concatBuilders $ map (mkDeclConst env) (constantLiterals gBinds)
      decDists    = concatBuilders $ map (mkDeclDistincts env) (groupBySorts (toListSEnv $ dLits si))
      decFuncs    = concatBuilders $ map (mkDeclFun env) (functionLiterals gBinds)
      qualifiers  = concatBuilders $ map (musfix env) (quals si)
      wfcs        = concatBuilders $ map (musfix env) (M.toList (ws si))
      horns       = concatBuilders $ map (musfix env) (M.toList (cm si))

-- | Environment for conversion
data ConvertEnv a = ConvertEnv {
  ceSInfo :: SInfo a,                           -- ^ The file info
  cePrettyVars :: (M.HashMap String String)     -- ^ Pretty names for known variables
  } deriving (Show)

-- | Gets the proper output name of a variable
safeVar :: ConvertEnv a -> Symbol -> String
safeVar env s = name
  where
    s'   = symbolString s
    subs = M.lookupDefault s' s' $ cePrettyVars env
    name = adjustName subs
    adjustName str
      | Just suffix <- L.stripPrefix "VV##" str       = "v" ++ suffix
      | Just suffix <- L.stripPrefix "lq_karg$" str   = mid suffix
      | Just suffix <- L.stripPrefix "fix$36$" str    = suffix
      | Just suffix <- L.stripPrefix "lit$36$" str    = suffix
      | Just suffix <- L.stripPrefix "lit$" str       = suffix
      | Just suffix <- L.stripPrefix "lit#" str       = suffix
      | otherwise                                     = str
      where
        mid xs = takeWhile isNotDelimiter xs
        isNotDelimiter '#' = False
        isNotDelimiter _   = True

-- | Gets the pretty name of a sort type
prettySort :: ConvertEnv a -> Symbol -> String
prettySort env s = M.lookupDefault s' s' $ cePrettyVars env
  where
    s' = case symbolString s of
        "[]" -> "List"
        s''  -> s''

class MusfixExport x where
  -- | Produces a lazy text builder for the given type in musfix format
  musfix :: ConvertEnv a -> x -> Builder

{- Global literals and functions -}
mkDeclFun :: ConvertEnv a -> (Symbol, Sort) -> Builder
mkDeclFun env (n, s) = build "(declare-fun {} {})\n" (safeVar env n, musfix env s)

mkDeclConst :: ConvertEnv a -> (Symbol, Sort) -> Builder
mkDeclConst env (n, s) = build "(declare-const {} {})\n" (safeVar env n, musfix env s)

mkDeclDistincts :: ConvertEnv a -> [Symbol] -> Builder
mkDeclDistincts env distincts = build "(assert (distinct {}))\n" (Only consts)
  where
    consts = concatBuildersS " " $ map mkConst distincts
    mkConst sym = build "{}" (Only $ safeVar env sym)


{- Sort declarations -}
instance MusfixExport DataDecl where
  musfix env d = build "(declare-sort {} {})\n" (name, numVars)
    where
      name = safeVar env $ symbol (ddTyCon d)
      numVars = ddVars d

{- Constraint types -}

-- | Builds qualifier
instance MusfixExport Qualifier where
  musfix env q = build "(qualif {} ({}) {})\n" (name, vars, body)
    where
      name = musfix env $ qName q
      vars = concatBuilders $ map (musfix env) (qParams q)
      body = musfix env $ qBody q

-- | Build qualifier parameter
instance MusfixExport QualParam where
  musfix env p = build "({} {})" (name, sort)
    where
      name = safeVar env $ qpSym p
      sort = musfix env $ qpSort p

-- | Build well-formedness constraint
instance MusfixExport (KVar, WfC a) where
  musfix env (k, wf) = build "(wf ${} ({}))\n" (symbolSafeText . kv $ k, vars)
    where
      vars        = concatBuilders $ map svar domain
      fmlSort     = sortBy (compare `on` fst)
      domain      = fmlSort $ sortedDomain ((bs . ceSInfo) env) wf
      svar (n, s) = build "({} {})" (safeVar env n, musfix env s)

-- | Build horn constraint
instance MusfixExport (SubcId, (SimpC a)) where
  musfix env (_, c) = build "(constraint (forall ({}) (=> {} {})))\n" (vars, lhs, rhs)
    where
      binds     = bs $ ceSInfo env
      lhsRefts  = clhs binds c

      vars = concatBuilders $ map sortedVar (filter isNotGlobalDef lhsRefts)
      isNotGlobalDef (s, _) = not $ hasGlobalDef (ceSInfo env) s

      sortedVar :: (Symbol, SortedReft) -> Builder
      sortedVar (s, sreft) = build "({} {})" (s', musfix env $ sr_sort sreft)
        where
          s' = safeVar env s
          
      lhs = combinedRefts (traceShowId lhsRefts)
      rhs = musfix env $ (traceShowId $ crhs c)

      -- | Combines all the lhs refinements into one and'd expression
      combinedRefts :: [(Symbol, SortedReft)] -> Builder
      combinedRefts xs = musfix env $ filterRedundantBools eAnds
        where
          eAnds = PAnd $ map expr xs
          expr :: (Symbol, SortedReft) -> Expr
          expr (s, sreft) = e'
            where
              Reft (_, e) = sr_reft sreft
              e' = (renameVar "v" s) e

{- Expressions -}

instance MusfixExport Symbol where
  musfix _                     = symbolBuilder

instance MusfixExport Sort where
  musfix _    FInt             = "Int"
  musfix _    (FVar n)         = build "@a{}" (Only n)
  musfix env  (FApp s s')      = mkAppS env s s'
  musfix env  (FTC f)          = build "{}" (Only $ prettySort env (symbol f))
  musfix env  (FObj a)         = build "@obj_{}" (Only $ musfix env a)
  musfix env  (FAbs _ s)       = build "{}" (Only $ musfix env s)
  musfix env  f@(FFunc _ _)    = build "({}) {}" (mkFuncArgsS env $ formalSortsFuncS f, musfix env $ returnSortFuncS f)
  musfix _    s                = build "unknown [given {}]" (Only $ show s)

mkFuncArgsS :: ConvertEnv a -> [Sort] -> Builder
mkFuncArgsS env srts           = concatBuildersS " " $ map b srts
  where
    b a = build "{}" (Only $ musfix env a)

mkAppS :: ConvertEnv a -> Sort -> Sort -> Builder
mkAppS env (FApp f' a') a      = build "({} {})" (mkApp' env 1 f' a', musfix env a)
  where
    mkApp' :: ConvertEnv a -> Int -> Sort -> Sort -> Builder
    mkApp' env d (FApp f' a') a  = build "{} {}" (mkApp' env (d + 1) f' a', musfix env a)
    mkApp' env d f a             = build "{}{} {}" (musfix env f, d + 1, musfix env a)
mkAppS env f a                 = build "({} {})" (musfix env f, musfix env a)


instance MusfixExport SymConst where
  musfix _    (SL t)           = build "{}" (Only t)

instance MusfixExport Constant where
  musfix _    (I i)            = build "{}" (Only i)
  musfix _    (R d)            = build "{}" (Only d)
  musfix _    (L t _ )         = build "{}" (Only t)

instance MusfixExport Bop where
  musfix _    Plus             = "+"
  musfix _    Minus            = "-"
  musfix _    Times            = "*"
  musfix _    Div              = "/"
  musfix _    RTimes           = "*"
  musfix _    RDiv             = "/"
  musfix _    Mod              = "mod"

instance MusfixExport Brel where
  musfix _    Eq               = "="
  musfix _    Ueq              = "="
  musfix _    Gt               = ">"
  musfix _    Ge               = ">="
  musfix _    Lt               = "<"
  musfix _    Le               = "<="
  musfix _    _                = error "export Brel: unknown"

instance MusfixExport Expr where
  musfix env  (ESym z)         = musfix env z
  musfix env  (ECon c)         = musfix env c
  musfix env  (EVar s)         = build "{}" (Only $ safeVar env s)

  -- special case for Set_empty application (TODO: Does mkApp break this?)
  musfix env  (EApp (ECst (EVar s) _) _)
    | safeVar env s == "Set_empty"  = "{}"

  musfix env  (EApp f a)       = mkApp env f a
  musfix env  (ENeg e)         = build "(- {})" (Only $ musfix env e)
  musfix env  (EBin o l r)     = build "({} {} {})" (musfix env o, musfix env l, musfix env r)
  musfix env  (EIte c t e)     = build "(ite {} {} {})" (musfix env c, musfix env t, musfix env e)
  musfix env  (ECst p _)       = build "{}" (Only $ musfix env p)
  musfix _    PTrue            = "True"
  musfix _    PFalse           = "False"
  musfix _    (PAnd [])        = "True"
  musfix env  (PAnd ps)        = mkAndOrs env "and" ps
  musfix _    (POr [])         = "False"
  musfix env  (POr ps)         = mkAndOrs env "or" ps
  musfix env  (PNot p)         = build "(not {})"   (Only $ musfix env p)
  musfix env  (PImp p q)       = build "(=> {} {})" (musfix env p, musfix env q)
  musfix env  (PIff p q)       = build "(= {} {})"  (musfix env p, musfix env q)
  musfix env  (PKVar k s)      = mkKVar env k s
  musfix env  (PAtom r e1 e2)  = mkRel env r e1 e2
  musfix _    e                = build "unsupported expression [{}]" (Only $ show e)

mkAndOrs :: ConvertEnv a -> LT.Text -> [Expr] -> Builder
mkAndOrs env _ [p]            = musfix env p
mkAndOrs env op (p1:p2:ps)    = build "({} {} {})" (op, musfix env p1, mkAndOrs env op (p2:ps))
mkAndOrs _   op _             = build "(empty {})" (Only op)

mkKVar :: ConvertEnv a -> KVar -> Subst -> Builder
mkKVar env k subst = build "(${} {})"    (symbolSafeText . kv $ k, args)
  where
    (Su m) = subst
    argSort = sortBy (compare `on` fst)
    args = concatBuildersS " " $ map ((musfix env) . snd) (argSort (M.toList m))

mkRel :: ConvertEnv a -> Brel -> Expr -> Expr -> Builder
mkRel env Ne  e1 e2 = mkNe env e1 e2
mkRel env Une e1 e2 = mkNe env e1 e2
mkRel env r   e1 e2 = build "({} {} {})" (musfix env r, musfix env e1, musfix env e2)

mkNe :: ConvertEnv a -> Expr -> Expr -> Builder
mkNe env e1 e2      = build "(not (= {} {}))" (musfix env e1, musfix env e2)

mkApp :: ConvertEnv a -> Expr -> Expr -> Builder
mkApp env (EApp f' a') a       = build "({} {})" (mkApp' env f' a', musfix env a)
  where
    mkApp' env (EApp f' a') a  = build "{} {}" (mkApp' env f' a', musfix env a)
    mkApp' env (ECst (EVar s) _) a 
      | s == "apply"           = musfix env a
    mkApp' env f a             = build "{} {}" (musfix env f, musfix env a)
mkApp env f a                  = build "({} {})" (musfix env f, musfix env a)

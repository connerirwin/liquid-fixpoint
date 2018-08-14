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


-- | Converts the given SInfo object into a MUSFix compatible string
convertToMusFix :: SInfo a -> String
convertToMusFix si = (LT.unpack (Builder.toLazyText (musfixFromInfo si)))

-- | Produce a lazy-text builder from the given SInfo
musfixFromInfo :: SInfo a -> Builder
musfixFromInfo si = build txt (qs, wfs, cs)
    where
      env = ConvertEnv {
              ceSInfo = si,
              ceSubs = M.empty,
              cePrettyVars = M.empty
            }
      txt = "; Qualifiers\n{}\n\n; Well-formedness constraints\n{}\n\n; Horn constraints\n{}"
      qs  = concatBuilders $ map (musfix env) (quals si)
      wfs = concatBuilders $ map (musfix env) (M.toList (ws si))
      cs  = concatBuilders $ map (musfix env) (M.toList (cm si))

-- | Environment for conversion
data ConvertEnv a = ConvertEnv {
  ceSInfo :: SInfo a,                           -- ^ The file info
  ceSubs :: (M.HashMap Symbol Symbol),          -- ^ Variable substitutions to perform
  cePrettyVars :: (M.HashMap Symbol Symbol)     -- ^ Pretty names for known variables
  } deriving (Show)

-- | Gets the proper output name of a variable
safeVar :: ConvertEnv a -> Symbol -> String
safeVar env s = name
  where
    subs = M.lookupDefault s s $ ceSubs env
    name = adjustName $ symbolString subs
    adjustName str
      | Just suffix <- L.stripPrefix "VV##" str       = "v" ++ suffix
      | Just suffix <- L.stripPrefix "lq_karg$" str   = mid suffix
      | otherwise                                     = str
      where
        mid xs = takeWhile isNotDelimiter xs
        isNotDelimiter '#' = False
        isNotDelimiter _   = True
  
class MusfixExport x where
  -- | Produces a lazy text builder for the given type in musfix format
  musfix :: ConvertEnv a -> x -> Builder

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
  musfix env (_, c) = build "(constraint (forall ({}) (=> {} {})))\n" (vars, lhs, musfix env $ crhs c)
    where
      binds = bs $ ceSInfo env
      vars = concatBuilders $ map sortedVar (clhs binds c)
      sortedVar :: (Symbol, SortedReft) -> Builder
      sortedVar (s, sreft) = build "({} {})" (s', musfix env $ sr_sort sreft)
        where
          s' = safeVar env s
      
      lhs :: Builder
      lhs = combinedRefts $ clhs binds c
      -- | Combines all the lhs refinements into one and'd expression
      combinedRefts :: [(Symbol, SortedReft)] -> Builder
      combinedRefts xs = musfix env e
        where
          e = PAnd $ map expr xs
          expr :: (Symbol, SortedReft) -> Expr
          expr (_, sreft) = e'
            where
              Reft (_, e') = sr_reft sreft

{- Expressions -}

instance MusfixExport Symbol where
  musfix _                = symbolBuilder
  
instance MusfixExport Sort where
  musfix _    FInt             = "Int"
  musfix _    (FVar n)         = build "@a{}" (Only n)
  musfix env  (FApp s s')      = build "{} {}" (musfix env s, musfix env s')
  musfix env  (FTC f)          = musfix env $ symbol f
  musfix _    s                = build "unknown [given {}]" (Only $ show s)
          
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
  musfix env  (EApp f a)       = build "({} {})" (musfix env f, musfix env a)
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
  
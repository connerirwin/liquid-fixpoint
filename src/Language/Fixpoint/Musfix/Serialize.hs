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

import Data.Semigroup
import Data.Text.Format
import Data.Text.Lazy.Builder (Builder)
import qualified Data.HashMap.Strict    as M
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as Builder

convertToMusFix :: SInfo a -> String
convertToMusFix si = (LT.unpack (Builder.toLazyText (musfixFromInfo si)))

safeVar :: Symbol -> String
safeVar s = "var_" ++ (symbolString s)

class MusfixExport a where
  -- | Produces a lazy text builder for the given type in musfix format
  musfix :: a -> Builder
  
{- File types -}
musfixFromInfo :: SInfo a -> Builder
musfixFromInfo si = build t (qs, wfs, horns)
    where
      t = ";Qualifiers\n{}\n\n;Well-formedness constraints\n{}\n\n;Constraints\n{}"
      qs :: Builder
      qs = foldl (<>) "" $ map musfix (quals si)
      wfs :: Builder
      wfs = foldl (<>) "" $ map musfix (M.toList (ws si))
      horns :: Builder
      horns = foldl (<>) "" $ map musfix (map prependBindEnv (M.toList (cm si)))
      prependBindEnv (k, v) = (bs si, k, v)
      
{- Constraint types -}
instance MusfixExport Qualifier where
  musfix q = build "(qualif {} ({}) {})\n" (name, varList, predicate)
    where
      name      = musfix $ qName q
      vars      = map musfix $ qParams q
      varList   = foldl (<>) "" vars
      predicate = musfix $ qBody q
      
instance MusfixExport QualParam where
  musfix p = build "({} {})" (name, sort)
    where
      name      = safeVar $ qpSym p
      sort      = musfix $ qpSort p
      
instance MusfixExport (KVar, WfC a) where
  musfix (k, wf) = build "(wf ${} {})\n" (symbolSafeText . kv $ k, var)
    where
      var :: Builder
      var = build "(({} {}))" (safeVar v, musfix s)
      (v, s, _) = wrft wf
  
instance MusfixExport (BindEnv, SubcId, (SimpC a)) where
  musfix (binds, _, c) = build "(constraint (forall ({}) (=> {} {})))\n" (vars, lhs, musfix $ crhs c)
    where
      vars :: Builder
      vars = foldl (<>) "" $ map sortedVar (clhs binds c)
      sortedVar :: (Symbol, SortedReft) -> Builder
      sortedVar (s, sreft) = build "({} {})" (s', musfix $ sr_sort sreft)
        where
          s' = safeVar s
      
      lhs :: Builder
      lhs = combinedRefts $ clhs binds c
      -- | Combines all the lhs refinements into one and'd expression
      combinedRefts :: [(Symbol, SortedReft)] -> Builder
      combinedRefts xs = musfix e
        where
          e = PAnd $ map expr xs
          expr :: (Symbol, SortedReft) -> Expr
          expr (_, sreft) = e'
            where
              Reft (_, e') = sr_reft sreft
      
      
instance MusfixExport (Symbol, SortedReft) where
  musfix (_, reft) = musfix $ sr_reft reft
  
instance MusfixExport Reft where
  musfix (Reft (_, e)) = musfix e
      
{- Expressions -}
instance MusfixExport Symbol where
  musfix = symbolBuilder
  
instance MusfixExport Sort where
  musfix s = r
    where
      r :: Builder
      r = case s of
          FInt    -> "Int"
          FVar n  -> build "@{}" (Only n)
          _       -> build "unknown [given {}]" (Only $ show s)
          
instance MusfixExport SymConst where
  musfix (SL t) = build "{}" (Only t)

instance MusfixExport Constant where
  musfix (I i)    = build "{}" (Only i)
  musfix (R d)    = build "{}" (Only d)
  musfix (L t _ ) = build "{}" (Only t)
  
instance MusfixExport Bop where
  musfix Plus     = "+"
  musfix Minus    = "-"
  musfix Times    = "*"
  musfix Div      = "/"
  musfix RTimes   = "*"
  musfix RDiv     = "/"
  musfix Mod      = "mod"
--  musfix op       = build "unknown bop [given {}]" (Only $ show op)

instance MusfixExport Brel where
  musfix Eq    = "="
  musfix Ueq   = "="
  musfix Gt    = ">"
  musfix Ge    = ">="
  musfix Lt    = "<"
  musfix Le    = "<="
  musfix _     = error "export Brel: unknown"
  
instance MusfixExport [Expr] where
  musfix es       = foldl (<>) "" $ map musfix es

instance MusfixExport Expr where
  musfix (ESym z)         = musfix z
  musfix (ECon c)         = musfix c
  musfix (EVar s)         = build "{}" (Only $ safeVar s)
  musfix (EApp f a)       = build "({} {})" (musfix f, musfix a)
  musfix (ENeg e)         = build "(- {})" (Only $ musfix e)
  musfix (EBin o l r)     = build "({} {} {})" (musfix o, musfix l, musfix r)
  musfix (EIte c t e)     = build "(ite {} {} {})" (musfix c, musfix t, musfix e)
  musfix (ECst e _)       = build "{}" (Only $ musfix e)
  musfix PTrue            = "True"
  musfix PFalse           = "False"
  musfix (PAnd [])        = "True"
  musfix (PAnd ps)        = mkAndOrs "and" ps
  musfix (POr [])         = "False"
  musfix (POr ps)         = mkAndOrs "or" ps
  musfix (PNot p)         = build "(not {})"   (Only $ musfix p)
  musfix (PImp p q)       = build "(=> {} {})" (musfix p, musfix q)
  musfix (PIff p q)       = build "(= {} {})"  (musfix p, musfix q)
  musfix (PAtom r e1 e2)  = mkRel r e1 e2
  musfix (PKVar k s)      = mkKVar k s
  musfix e                = build "unsupported expression [{}]" (Only $ show e)
  
mkAndOrs :: LT.Text -> [Expr] -> Builder
mkAndOrs _ [p]            = musfix p
mkAndOrs op (p1:p2:ps)    = build "({} {} {})" (op, musfix p1, mkAndOrs op (p2:ps))
mkAndOrs op _             = build "(empty {})" (Only op)

mkKVar :: KVar -> Subst -> Builder
mkKVar k subst = build "(${} {})"    (symbolSafeText . kv $ k, args)
  where
    (Su m) = subst
    -- TODO: This will not be ordered right!
    args :: Builder
    args = case foldl space Nothing $ map musfix (M.elems m) of
      Nothing -> ""
      Just as -> as
    space Nothing  r = Just $ build "{}" (Only r)
    space (Just l) r = Just $ build "{} {}" (l, r)
  
mkRel :: Brel -> Expr -> Expr -> Builder
mkRel Ne  e1 e2 = mkNe e1 e2
mkRel Une e1 e2 = mkNe e1 e2
mkRel r   e1 e2 = build "({} {} {})" (musfix r, musfix e1, musfix e2)

mkNe :: Expr -> Expr -> Builder
mkNe e1 e2      = build "(not (= {} {}))" (musfix e1, musfix e2)
  
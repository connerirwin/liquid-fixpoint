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
      horns :: String
      horns = "TODO"
      
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
      name      = musfix $ qpSym p
      sort      = musfix $ qpSort p
      
instance MusfixExport (KVar, WfC a) where
  musfix (k, wf) = build "(wf ${} {})" (symbolSafeText . kv $ k, show $ wrft wf)
      
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
  musfix (EVar s)         = musfix s
  musfix (EApp f a)       = build "({} {})" (musfix f, musfix a)
  musfix (ENeg e)         = build "(- {})" (Only $ musfix e)
  musfix (EBin o l r)     = build "({} {} {})" (musfix o, musfix l, musfix r)
  musfix (EIte c t e)     = build "(ite {} {} {})" (musfix c, musfix t, musfix e)
  musfix PTrue            = "True"
  musfix PFalse           = "False"
  musfix (PAnd [])        = "True"
  musfix (PAnd ps)        = build "(and {})"   (Only $ musfix ps)
  musfix (POr [])         = "False"
  musfix (POr ps)         = build "(or  {})"   (Only $ musfix ps)
  musfix (PNot p)         = build "(not {})"   (Only $ musfix p)
  musfix (PImp p q)       = build "(=> {} {})" (musfix p, musfix q)
  musfix (PIff p q)       = build "(= {} {})"  (musfix p, musfix q)
  musfix (PAtom r e1 e2)  = mkRel r e1 e2
  musfix e                = build "unsupported expression [{}]" (Only $ show e)
  
mkRel :: Brel -> Expr -> Expr -> Builder.Builder
mkRel Ne  e1 e2 = mkNe e1 e2
mkRel Une e1 e2 = mkNe e1 e2
mkRel r   e1 e2 = build "({} {} {})" (musfix r, musfix e1, musfix e2)

mkNe :: Expr -> Expr -> Builder.Builder
mkNe e1 e2      = build "(not (= {} {}))" (musfix e1, musfix e2)
  
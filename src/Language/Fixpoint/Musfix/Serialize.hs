{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.Serialize (
  convertToMusFix
  ) where

import Language.Fixpoint.Musfix.Translate
import Language.Fixpoint.Musfix.Types
import Language.Fixpoint.Musfix.Util

import Data.Text.Format

import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy                    as LT
import qualified Data.Text.Lazy.Builder            as Builder
import qualified Language.Fixpoint.Types           as LFP

-- | Converts the given SInfo object into a MUSFix compatible string
convertToMusFix :: LFP.SInfo a -> String
convertToMusFix si = (LT.unpack (Builder.toLazyText (musfix $ musfixInfo si)))
      
class MusfixExport a where
  -- | Produces a lazy text builder for the given type in musfix format
  musfix :: a -> Builder
  
instance MusfixExport MusfixInfo where
  musfix mi = build txt (txtSorts, txtConsts, txtDstnct, txtFuncs, txtQuals, txtWfCs, txtHorns)
    where
      --txt = "; Uninterpreted Sorts\n{}{}\n\n; Constants\n{}\n\n; Distinct Constants\n{}\n\n; Uninterpreted Functions\n{}\n\n; Qualifiers\n{}  \n\n; Well-formedness Constraints\n{}\n\n; Horn Constraints\n{}"
      txt = "; Sorts\n{}\n\n; Constants\n{}\n\n{}\n\n; Uninterpreted Functions\n{}\n\n; Qualifiers\n{}\n\n; Well-formedness Constraints\n{}\n\n;  Constraints\n{}\n\n"
      txtSorts  = concatBuildersS "\n" $ map musfix (sorts mi)
      txtConsts = concatBuildersS "\n" $ map musfix (constants mi)
      txtDstnct = concatBuildersS "\n" $ map musfix (distincts mi)
      txtFuncs  = concatBuildersS "\n" $ map musfix (functions mi)
      txtQuals  = concatBuildersS "\n" $ map musfix (qualifiers mi)
      txtWfCs   = concatBuildersS "\n" $ map musfix (wfConstraints mi)
      txtHorns  = concatBuildersS "\n" $ map musfix (constraints mi)
      
instance MusfixExport Sort where
  musfix IntS              = "Int"
  musfix BoolS             = "Bool"
  musfix (VarS n)          = build "@a{}" (Only n)
  musfix (TypeConS n [])   = build "{}"  (Only n)
  musfix (TypeConS n xs)   = build "({} {})" (n, concatBuildersS " " $ map musfix xs)
  
instance MusfixExport SortDecl where
  musfix (SortDecl name num) = build "(declare-sort {} {})" (name, num)
  
instance MusfixExport Const where
  musfix (Const name srt)  = build "(declare-const {} {})" (name, musfix srt)
  
instance MusfixExport Distincts where
  musfix (Distincts consts) = build "(assert (distinct {}))" (Only (concatBuildersS " " $ map constName consts))
    where
      constName (Const name _) = build "{}" (Only name)
  
instance MusfixExport Func where
  musfix (Func name args ret) = build "(declare-fun {} ({}) {})" (name, concatBuildersS " " $ map musfix args, musfix ret)
  
instance MusfixExport Var where
  musfix (Var name srt) = build "({} {})" (name, musfix srt)
  
instance MusfixExport Expr where
  musfix (SymbolExpr name) = build "{}" (Only name)
  musfix (AppExpr f args)  = build "({} {})" (musfix f, args')
    where
      args' = concatBuildersS " " $ map musfix args
  
instance MusfixExport Qual where
  musfix (Qual name args expr) = build "(qualif {} ({}) {})" (name, concatBuilders $ map musfix args, musfix expr)
      
instance MusfixExport WfC where
  musfix (WfC name vars) = build "(wf {} ({}))" (name, concatBuilders $ map musfix vars)
  
instance MusfixExport HornC where
  musfix (HornC vars expr) = build "(constraint (forall ({}) {}))" (concatBuilders $ map musfix vars, musfix expr)

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

module Language.Fixpoint.Musfix.Types (
    MusfixInfo (..),
    Sort (..),
    SortDecl (..),
    Expr (..),
    Var (..),
    Qual (..),
    Const (..),
    Distincts (..),
    Func (..),
    WfC (..),
    HornC (..),
    Id
  ) where


import qualified Data.Text.Lazy         as LT

type Id = LT.Text

-- | Musfix info translated from SInfo
data MusfixInfo = MusfixInfo {
  qualifiers :: [Qual],
  constants  :: [Const],
  distincts  :: [Distincts],
  functions  :: [Func],
  wfConstraints :: [WfC],
  constraints :: [HornC],
  sorts :: [SortDecl]
}

-- | Musfix sorts
data Sort = IntS | BoolS | VarS Id | TypeConS Id [Sort] deriving (Show)

-- | Sort declaration
data SortDecl = SortDecl Id Int

-- | Musfix expressions
data Expr = 
    SymbolExpr  Id
  | AppExpr     Expr [Expr]
  deriving (Show, Eq)
  
-- | Musfix sorted var
data Var = Var Id Sort

-- | Musfix qualifier
data Qual = Qual Id [Var] Expr

-- | Musfix constant
data Const = Const Id Sort

-- | Mustfix distinct
data Distincts = Distincts [Const]

-- | Musfix functions
data Func = Func Id [Sort] Sort

-- | Musfix well-formedness constraint
data WfC = WfC Id [Var]

-- | Musfix horn constraint
data HornC = HornC [Var] Expr

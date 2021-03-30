{-# LANGUAGE GADTs #-}

module TypedLawAST where

import Prelude (Char, Double, Integer, String, Maybe, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read)
import Data.Map

import qualified AbsSie as UT
{-
type LawName = String

type LawMap = Map LawName Law

data Law = DLaw [Parameter] Term ImpRel Term

--data Parameter = DParameter PName PType


data Variable
  | IntExpr
  | ValueContext
  | Context
  | Term -- ev ej helt konkret
  | VariableSet
  | Value

data ParameterValue where
  DParameterValue :: ParameterName t -> t -> ParameterValue
-}

data Command
  = AlphaEquiv
--  | Law LawTerm LawTerm Substitutions
  deriving (C.Eq, C.Ord, C.Show, C.Read)
-- Lägg till fler senare


{- Något sånthär för substitutions.
-- Vänd på lagar när man går från höger till vänster
data AppliedLaw = DAppliedLaw Substitutions From ImpRel To
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type ImpRel = UT.ImpRel

type From = UT.Term
type To = UT.Term
type Term = UT.Term

type Substitutions = [(UT.VarAnyType, UT.Term)]
-}
{-
-unfold-1: let G {x =[v,w]= V} in C[x] |~> let G {x =[v,w]= V} in C[{x}d^V];

data Term
    = TValueMetaVar MVValue
    | TAppCtx MVContext Term
    | TLet LetBindings Term
    | TDummyBinds VarSet Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBindings
    = LBSBoth [MetaBindSet] [LetBinding]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data MetaBindSet
    = MBSMetaVar MVLetBindings | MBSSubstitution MVLetBindings Var Var
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBinding = DLetBinding Var BindSymbol Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBinding = DLetBinding Var BindSymbol Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data BindSymbol = BSWeights UT.StackWeight UT.HeapWeight | BSNoWeight
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type StackWeight = IntExpr

type HeapWeight = IntExpr

data IntExpr
  = IEVar IntegerVar
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type IntegerVar = MVIntegerVar

newtype MVIntegerVar = MVIntegerVar String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)
-}

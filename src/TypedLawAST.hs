{-# LANGUAGE GADTs #-}

module TypedLawAST where

import qualified AbsSie as UT
import Data.Map

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

data AppliedLaw = DAppliedLaw [(UT.VarAnyType, Term)] Term ImpRel Term

data Term = Ts

type ImpRel = UT.ImpRel

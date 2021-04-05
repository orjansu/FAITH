module TypedLawAST where

import Prelude (Char, Double, Integer, String, Maybe, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read, show)
import Data.Map

import qualified AbsSieLaws as UTLaw

type LawName = String

type LawMap = Map LawName Law

data Law = DLaw Term UTLaw.ImpRel Term
-- TODO ImpRel
-- -unfold-1: let G {x =[v,w]= V} in C[x] |~> let G {x =[v,w]= V} in C[{x}d^V];

data Term
    = TValueMetaVar UTLaw.MVValue
    | TAppCtx UTLaw.MVContext Term
    | TLet LetBindings Term
    | TDummyBinds VarSet Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Var = UTLaw.MVVar

data VarSet
  = VSConcrete [Var]
  deriving (C.Eq, C.Ord, C.Show, C.Read)
  -- TODO expand

data LetBindings
    = LBSBoth MetaBindSet [LetBinding] --TODO expand to [MetaBindSet]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data MetaBindSet
    = MBSMetaVar UTLaw.MVLetBindings
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBinding = DLetBinding Var StackWeight HeapWeight Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type StackWeight = IntExpr

type HeapWeight = IntExpr

data IntExpr
  = IEVar IntegerVar
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type IntegerVar = UTLaw.MVIntegerVar

module TypedLawAST where

import Prelude (Char, Double, Integer, String, Maybe, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read)
import Data.Map (Map)
import Data.Set (Set)

import qualified AbsSieLaws as UTLaw
import Common (ImpRel)

type LawName = String

type LawMap = Map LawName Law

data Law = DLaw LawName Term ImpRel Term SideCond
  deriving (C.Eq, C.Ord, C.Show, C.Read)
-- -unfold-1: let G {x =[v,w]= V} in C[x] |~> let G {x =[v,w]= V} in C[{x}d^V];

data Term
    = TValueMetaVar String
    | TGeneralMetaVar String
    | TNonTerminating
    | TNum Integer
    | TConstructor Constructor
    | TVar String
    | TAppCtx String Term
    | TAppValCtx String Term
    | TLet LetBindings Term
    | TLam String Term
    | TDummyBinds VarSet Term
    | TStackSpikes IntExpr Term
    | THeapSpikes IntExpr Term
    | TSubstitution Term String String
    | TRedWeight IntExpr Reduction
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Reduction
  = RMetaVar String Term
  | RApp Term String
  | RPlusW Term IntExpr Term
  | RAddConst IntExpr Term
  | RIsZero Term
  | RSeq Term Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Name = String
type Arguments = String

data Constructor
  = CGeneral Name Arguments
  | CTrue
  | CFalse
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Var = String

data VarSet
  = VSConcrete (Set Var)
  deriving (C.Eq, C.Ord, C.Show, C.Read)
  -- TODO expand

data LetBindings
    = LBSBoth [MetaBindSet] [LetBinding] --TODO expand to [MetaBindSet]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data MetaBindSet
    = MBSMetaVar String
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type LetBinding = (Var, StackWeight, HeapWeight, Term)

type StackWeight = IntExpr

type HeapWeight = IntExpr

data IntExpr
  = IEVar String
  | IENum Integer
  | IEPlus IntExpr IntExpr
  | IEMinus IntExpr IntExpr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data SideCond = NoSideCond
  deriving (C.Eq, C.Ord, C.Show, C.Read)

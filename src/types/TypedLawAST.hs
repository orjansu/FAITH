
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

data Term
    = TValueMetaVar String
    | TGeneralMetaVar String
    | TMVTerms String
    | TVar String
    | TAppCtx String Term
    | TAppValCtx String Term
    | TNonTerminating
    | TNum Integer
    | TConstructor Constructor
    | TStackSpikes IntExpr Term
    | THeapSpikes IntExpr Term
    | TDummyBinds VarSet Term
    | TSubstitution Term String String
    | TLam String Term
    | TLet LetBindings Term
    | TRedWeight IntExpr Reduction
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Reduction
  = RMetaVar String Term
  | RApp Term String
  | RPlusW Term IntExpr Term
  | RCase Term [CaseStm]
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
type MVLetBindings = String

data VarSet
  = VSConcrete (Set Var)
  | VSMetaVar String
  | VSFreeVars VarContainer
  | VSDomain MVLetBindings
  | VSUnion VarSet VarSet
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VarContainer
  = VCTerm Term
  | VCMetaVarContext String
  | VCMetaVarRed String
  | VCValueContext String
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBindings
    = LBSBoth [MetaBindSet] [LetBinding]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data MetaBindSet
    = MBSMetaVar String
    | MBSSubstitution String Var Var
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type LetBinding = (Var, StackWeight, HeapWeight, Term)

type StackWeight = IntExpr

type HeapWeight = IntExpr

data CaseStm
  = CSAlts String
  | CSPatterns String Term
  | CSConcrete Constructor Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data IntExpr
  = IEVar String
  | IENum Integer
  | IEPlus IntExpr IntExpr
  | IEMinus IntExpr IntExpr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data SideCond
  = NoSideCond
  | WithSideCond BoolTerm
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data BoolTerm
  = BTSizeEq MVLetBindings MVLetBindings
  | BTSetEq VarSet VarSet
  | BTSubsetOf VarSet VarSet
  | BTIn Var VarSet
  deriving (C.Eq, C.Ord, C.Show, C.Read)

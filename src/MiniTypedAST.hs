{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MiniTypedAST where
-- contains only the constructs needed for the POC proofs
-- Does not contain datatypes for the proof rules.

import Prelude (Char, Double, Integer, String, Maybe, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String
import Data.Map.Strict (Map)
import Data.Set (Set)

import qualified TypedLawAST as Law

type Var = Name
type Name = String

data ProofScript = DProofScript [ProgBinding] [Theorem]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ProgBinding = DProgBinding CapitalIdent LetBindings
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype CapitalIdent = CapitalIdent String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

type LetBindings = [(Name, StackWeight, HeapWeight, Term)]

type StackWeight = Integer

type HeapWeight = Integer

type SubTerm = Term

data Term
    = TVar Var
    | TNum Integer --A
    | TLam Var Term
    | THole --Ctx
    | TLet LetBindings Term --A
    | TDummyBinds VarSet Term --A
    | TRedWeight RedWeight Red --A
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type VarSet = Set Var

data Red
    = RApp Term Var
    | RPlusWeight Term RedWeight Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type RedWeight = Integer --I will add expressions here later

data Theorem = DTheorem Proposition Proof
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type HasContext = Bool -- desugar it to a let in the start and end term

data Proposition = DProposition HasContext FreeVars Start ImpRel Goal
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data FreeVars = DFreeVars VarSet
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Start = DStart Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Goal  = DGoal  Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

-- Just do simple proof method for now.
data Proof = DProof [(ImpRel, Term, Law.AppliedLaw)]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

-- Just deals with these two right now.
data ImpRel
    = DefinedEqual
    | StrongImprovementLR
  deriving (C.Eq, C.Ord, C.Show, C.Read)

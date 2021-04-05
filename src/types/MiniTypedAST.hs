{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MiniTypedAST where
-- contains only the constructs needed for the POC proofs
-- Does not contain datatypes for the proof rules.

import Prelude (Char, Double, Integer, String, Maybe, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read, show)
import qualified Data.String
import Data.Map.Strict (Map)
import Data.Set (Set)

import qualified TypedLawAST as Law
import Common (ImpRel)

type Var = Name
type Name = String

-- letBindings are put into each term instead
-- later maybe put the set of laws here
data ProofScript = DProofScript [Theorem]
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
-- TODO derive a better show function that converts to AbsSie and then uses
-- the pretty-printer (showTree)

type VarSet = Set Var

data Red
    = RApp Term Var
    | RPlusWeight Term RedWeight Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type RedWeight = Integer --I will add expressions here later

data Theorem = DTheorem Proposition Proof
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Proposition = DProposition FreeVars Start ImpRel Goal
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type TermVars = Set String
type VarVars = Set String

data FreeVars = DFreeVars TermVars VarVars
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Start = Term
type Goal  = Term

-- Endast alpha-equiv just nu.
data Proof
  = Simple SubProof
  -- | Induction SubProof SubProof
  -- | Custom ...?
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type SubProof = [ProofStep]

data ProofStep
  = PSMiddle Term SubTerm Command ImpRel Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)


data Command
  = AlphaEquiv
  | Law Law.Law Substitutions
  deriving (C.Eq, C.Ord, C.Read)
-- Lägg till fler senare

data Substitutions = Set (String, Term)
  deriving (C.Eq, C.Ord, C.Read)

-- TODO add show in law later.
instance C.Show Command where
  show AlphaEquiv = "-alpha-equiv"

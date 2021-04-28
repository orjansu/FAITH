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
    = TNonTerminating
    | TVar Var
    | TNum Integer
    | TLam Var Term
    | THole
    | TLet LetBindings Term
    | TDummyBinds VarSet Term
    | TStackSpikes IntExpr Term
    | THeapSpikes IntExpr Term
    | TRedWeight RedWeight Red
  deriving (C.Eq, C.Ord, C.Show, C.Read)

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

type Context = Term
data ProofStep
  = PSMiddle Term Command ImpRel Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)


data Command
  = AlphaEquiv
  | Law Context Law.Law Substitutions
  deriving (C.Eq, C.Ord, C.Read)
-- Lägg till fler senare

-- TODO add show in law later.
instance C.Show Command where
  show AlphaEquiv = "-alpha-equiv"
  show (Law _ (Law.DLaw lawName _ _ _ _) _) = lawName

type Substitutions = Map String Substitute

data Substitute
  = SLetBindings LetBindings
  | SValue Term
  | SContext Term
  | SIntegerVar IntExpr
  | SVar String
  | SVarSet (Set String) -- Not used yet
  | STerm Term
--  | SVarVect TODO support the following later:
--  | SValueContext
--  | SReduction
--  | SPattern
--  | SCaseStm
--  | SConstructorName
  deriving (C.Eq, C.Ord, C.Read)

data IntExpr
  = IENum Integer
  deriving (C.Eq, C.Ord, C.Read, C.Show)


{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}

module TypedAST where

import qualified AbsSie as UT

data ProofScript = PS

--S = specification
--Ctx = Context
--Con = concrete
--L = only in law file
--A = anywhere
--Sug = syntactic sugar
-- Antar att Var -> Metavar i Laws

class Specification a
class Context a
class Concrete a
class Law a

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

newtype CapitalIdent = CapitalIdent String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

newtype CommandName = CommandName String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

data ProofScript = DProofScript ProgBindings [Theorem]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ProgBindings = DProgBindings [ProgBinding]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ProgBinding = DProgBinding CapitalIdent LetBindings
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBindings
    = LBSAny | LBSVar CapitalIdent | LBSSet [LetBinding]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LetBinding = LBAny | LBConcrete Ident BindSymbol Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data BindSymbol = BSWeights StackWeight HeapWeight | BSNoWeight
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data StackWeight = StackWeightExpr IntExpr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data HeapWeight = HeapWeightExpr IntExpr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data IntExpr
    = IEAny --S
    | IEVar Ident -- S Ctx Con
    | IENum Integer --A
    | IEPlus IntExpr IntExpr --A
    | IEMinus IntExpr IntExpr --A
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data RedWeight = DRedWeight StackWeight --
  deriving (C.Eq, C.Ord, C.Show, C.Read)



data Term
    = TAny --S
    | TTermVar CapitalIdent -- S, Ctx, Con
    | TNonTerminating -- A
    | TVar Ident -- S, Ctx, Con
    | TNum Integer --A
    | THole --Ctx
    | TConstructor Constructor --A
    | TLam Ident Term -- A, Ctx, Con
    | TLet LetBindings Term --A
    | TStackSpike Term --A, Sug
    | TStackSpikes StackWeight Term --A
    | THeapSpike Term --A, Sug
    | THeapSpikes HeapWeight Term --A
    | TDummyBinds VarSet Term --A
    | TRedWeight RedWeight Red --A
    | TRed Red --A, Sug
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Red
    = RCase Term [CaseStm] --A
    | RApp Term Var --A
    | RAppInd Var IndExpr Var --A
    | RAddConst Integer Term --A
    | RIsZero Term --A
    | RSeq Term Term --A
    | RPlusWeight Term RedWeight Term --A
    | RPlus Term Term --A, Sug
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data IndExpr = DIndExpr IntExpr --A, ev ta bort
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Constructor
    = CGeneral CapitalIdent [Var] -- S Ctx Con
    | CCons Ident Ident -- S Ctx Con
    | CTrue | CFalse --A
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Var = DVar Ident --S Ctx Con. Metavar för L.
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VarSet = DVarSet [Var] --S Ctx Con
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CaseStm = CaseStmAlts -- L
             | CaseStmConcrete Constructor Term --A
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Theorem = DTheorem Proposition Proof
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Proposition = DProposition InContext Term ImpRel Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Proof = DProof CommandName [CmdArgument] [SubProof] Qed
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Qed = DQed
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data InContext = WithContext CapitalIdent | NoContext
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ImpRel
    = DefinedEqual
    | StrongImprovementLR
    | WeakImprovementLR
    | StrongImprovementRL
    | WeakImprovementRL
    | StrongCostEquiv
    | WeakCostEquiv
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CmdArgument = CAValue CmdValue | CAAssign CmdAssignee CmdValue
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CmdValue
    = CVTermOrCtx Term | CVLetBindings LetBindings | CVVarSet VarSet
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CmdAssignee = CASmallVar Ident | CABigVar CapitalIdent
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data SubProof = DSubProof CommandName [ProofStep]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ProofStep
    = PSOn SubTerm CommandName [CmdArgument]
    | PSFirstTerm Term
    | PSTerm ImpRel Term
    | PSHereMarker
    | PSQed Qed
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data SubTerm = STWhole | STTerm Term | STGuess
  deriving (C.Eq, C.Ord, C.Show, C.Read)

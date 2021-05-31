{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module LocallyNameless where


import Prelude (Char, Double, Integer, String, Maybe, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String
import Data.Set (Set)

type Distance = Integer
type VarIndex = Integer

type VarName = String
data Var
  = LambdaVar Distance
  | LetVar Distance VarIndex
  | CaseConstructorVar Distance VarIndex
  | FreeVar VarName
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype CapitalIdent = CapitalIdent String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

type LetBindings = [(StackWeight, HeapWeight, Term)]

type StackWeight = Integer

type HeapWeight = Integer

type SubTerm = Term

type ConstructorName = String

data Term
    = TNonTerminating
    | TVar Var
    | TNum Integer
    | TConstructor ConstructorName [Var]
    | TLam Term
    | THole
    | TLet LetBindings Term
    | TDummyBinds VarSet Term
    | TStackSpikes StackWeight Term
    | THeapSpikes HeapWeight Term
    | TRedWeight RedWeight Red
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type VarSet = Set Var

data Red
    = RApp Term Var
    | RCase Term [(ConstructorName, Term)]
    | RPlusWeight Term RedWeight Term
    | RAddConst Integer Term
    | RIsZero Term
    | RSeq Term Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type RedWeight = Integer

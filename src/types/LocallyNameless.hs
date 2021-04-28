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

data Term
    = TVar Var
    | TNum Integer --A
    | THole --Ctx
    | TLam Term
    | TLet LetBindings Term --A
    | TDummyBinds VarSet Term --A
    | TRedWeight RedWeight Red --A
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type VarSet = Set Var

data Red
    = RApp Term Var
    | RPlusWeight Term RedWeight Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type RedWeight = Integer

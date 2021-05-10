{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE LambdaCase #-}

module TermCorrectness ( checkTypedTerm
                       , checkBoundVariablesDistinct
                       , checkFreeVars
                       , getBoundVariables
                       , numHoles
                       , isValue
                       , getAllMetaVars
                       , getFreeVariables
                       , getAllVariables
                        ) where

import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified Data.Set as Set
import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Data.List (unzip4)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import CheckMonad (assert, assertTerm)
import OtherUtils (applyOnSubtermsM, applyOnSubterms)

-- | given M and S, where S is the set of variables that are allowed to be free
-- in M, checks that:
-- - Does checks of checkFreeVars and checkBoundVariablesDistinct
-- - Checks that it is not a context
-- - Does not: Check typing of a simply typed lambda calculus
-- - General terms, i.e. any(M) are declared free (TODO)
checkTypedTerm :: (MonadError String m, Log.MonadLogger m, HasCallStack) =>
                  T.Term -> Set.Set String -> m ()
checkTypedTerm term expectedFreeVars = do
  checkBoundVariablesDistinct term
  checkFreeVars term expectedFreeVars
  assertTerm (numHoles term == 0)
    "Top-level terms should not be contexts" term

-- | given M, checks that the names of all bound variables in M are distinct.
--
-- Does not check anything else.
checkBoundVariablesDistinct :: (MonadError String m, HasCallStack) =>
                               T.Term -> m ()
checkBoundVariablesDistinct term =
  let res = (flip evalState) Set.empty $ runExceptT $ checkBoundVars term
  in case res of
    Left str -> throwError $ "the bound name "++str
                              ++" is bound at least twice in "
                       ++showTypedTerm term
    Right () -> return ()
  where
    checkBoundVars :: T.Term -> ExceptT String (State (Set.Set String)) ()
    checkBoundVars = \case
      T.TLam var term            -> do
        checkBoundVar var
        checkBoundVars term
      T.TLet letBindings term    -> do
        mapM checkBVLB letBindings
        checkBoundVars term
        where
          checkBVLB (name, sw, hw, term) = do
            checkBoundVar name
            checkBoundVars term
      T.TRedWeight redWeight (T.RCase term branches) -> do
        let (_cNames, args, terms) = unzip3 branches
        mapM checkBoundVar $ concat args
        mapM checkBoundVars terms
        return ()
      nonBindingTerm -> applyOnSubtermsM nonBindingTerm
                                         ()
                                         checkBoundVars
                                         (const ())

    checkBoundVar :: (MonadError String m, MonadState (Set.Set String) m) =>
                      String -> m ()
    checkBoundVar name = do
      boundVars <- get
      if Set.member name boundVars
        then throwError name
        else do
          let boundVars' = Set.insert name boundVars
          put boundVars'

-- | Checks that all variables are declared free or bound.
-- Also checks that no bound variable shadows a free variable.
-- Given M and S, checks that:
-- FV(M) `isSubsetOf` S && BV(M) `disjoint` S
checkFreeVars :: (MonadError String m, Log.MonadLogger m, HasCallStack) =>
                 T.Term -> Set.Set String -> m ()
checkFreeVars term expectedFreeVars = do
  let (_lnlTerm, actualFreeVars) = toLocallyNameless term
  assert (actualFreeVars `Set.isSubsetOf` expectedFreeVars)
    $ "All free variables should be declared. "
      ++"In term "++showTypedTerm term++"\n, "++" Variable(s) "
      ++show (Set.difference actualFreeVars expectedFreeVars)
      ++" should be declared free if intended."
  let boundVariables = getBoundVariables term
  assert (expectedFreeVars `Set.disjoint` boundVariables)
    $ "You may not shadow a free variable. In term "++showTypedTerm term++"\n"
      ++"Variable(s) "
      ++show (expectedFreeVars `Set.intersection` boundVariables)
      ++" shadows a free variable."
      ++"expectedFreeVars= "++show expectedFreeVars
      ++"boundVariables = "++show boundVariables

-- | Returns the set of bound variables in a term.
-- does no further checks on the correctness of the term.
getBoundVariables :: T.Term -> Set.Set String
getBoundVariables = \case
  T.TLam var term -> Set.singleton var `Set.union` getBoundVariables term
  T.TLet letBindings term -> boundVarsLBS `Set.union` getBoundVariables term
    where
      boundVarsLBS = Set.unions . map getLBBound $ letBindings
      getLBBound (var, _sw, _hw, term) =
        Set.singleton var `Set.union` getBoundVariables term
  T.TRedWeight _ (T.RCase term branches) ->
    let boundInTerm = getBoundVariables term
        (_cNames, args, terms) = unzip3 branches
        boundInCase = Set.fromList $ concat args
        boundInTerms = Set.unions $ map getBoundVariables terms
    in Set.unions [boundInTerm, boundInCase, boundInTerms]
  nonBindingTerm -> applyOnSubterms nonBindingTerm
                                    Set.empty
                                    getBoundVariables
                                    Set.unions

-- | Returns the number of holes in a term or context
numHoles :: T.Term -> Integer
numHoles (T.THole) = 1
numHoles nonHole = applyOnSubterms nonHole
                                   0
                                   numHoles
                                   sum

isValue :: T.Term -> Bool
isValue (T.TNonTerminating)              = False
isValue (T.TVar _var)                    = False
isValue (T.TNum _integer)                = True
isValue (T.TConstructor _ _)             = True
isValue (T.TLam _var _term)              = True
isValue (T.THole)                        = False
isValue (T.TLet _letBindings _term)      = False
isValue (T.TDummyBinds _varSet _term)    = False
isValue (T.TStackSpikes _sw _term)       = False
isValue (T.THeapSpikes _hw _term)        = False
isValue (T.TRedWeight _redWeight _redFD) = False

getAllMetaVars :: Law.Law -> Set.Set String
getAllMetaVars = \case
  Law.DLaw _name term1 _imprel term2 sideCondition ->
    Set.unions [getMetaVars term1, getMetaVars term2, getMetaVars sideCondition]

class MetaVarContainer a where
  getMetaVars :: a -> Set.Set String

instance MetaVarContainer Law.Term where
  getMetaVars = \case
    Law.TValueMetaVar mvName -> Set.singleton mvName
    Law.TGeneralMetaVar mvName -> Set.singleton mvName
    Law.TMVTerms mvName -> Set.singleton mvName
    Law.TVar mvName -> Set.singleton mvName
    Law.TAppCtx mvName term ->
      Set.singleton mvName `Set.union` getMetaVars term
    Law.TAppValCtx metaV term ->
      Set.singleton metaV `Set.union` getMetaVars term
    Law.TNonTerminating -> Set.empty
    Law.TNum _ -> Set.empty
    Law.TConstructor (Law.CGeneral name args) -> Set.fromList [name, args]
    Law.TStackSpikes iexpr term -> getMetaVars iexpr
                                     `Set.union` getMetaVars term
    Law.THeapSpikes iexpr term -> getMetaVars iexpr
                                     `Set.union` getMetaVars term
    Law.TDummyBinds lVarSet term ->
      getMetaVars lVarSet `Set.union` getMetaVars term
    Law.TSubstitution term x y -> getMetaVars term
                                    `Set.union` Set.fromList [x,y]
    Law.TLam var term -> Set.insert var $ getMetaVars term
    Law.TLet letBindings term -> getMetaVars letBindings
                                   `Set.union` getMetaVars term
    Law.TRedWeight iexpr reduction -> Set.unions [getMetaVars iexpr
                                                 , getMetaVars reduction]


instance MetaVarContainer Law.IntExpr where
  getMetaVars (Law.IEVar mv) = Set.singleton mv
  getMetaVars (Law.IENum _) = Set.empty
  getMetaVars (Law.IESizeBind metaG) = Set.singleton metaG
  getMetaVars (Law.IEPlus ie1 ie2) = getMetaVars ie1 `Set.union` getMetaVars ie2
  getMetaVars (Law.IEMinus ie1 ie2) = getMetaVars ie1
                                        `Set.union` getMetaVars ie2

instance MetaVarContainer Law.VarSet where
  getMetaVars (Law.VSConcrete varSet) = varSet
  getMetaVars (Law.VSMetaVar metaX) = Set.singleton metaX
  getMetaVars (Law.VSVectMeta xs) = Set.singleton xs
  getMetaVars (Law.VSFreeVars varContainer) = getMetaVars varContainer
  getMetaVars (Law.VSDomain metaG) = Set.singleton metaG
  getMetaVars (Law.VSUnion lVarSet1 lVarSet2) =
    getMetaVars lVarSet1 `Set.union` getMetaVars lVarSet2
  getMetaVars (Law.VSDifference lVarSet1 lVarSet2) =
    getMetaVars lVarSet1 `Set.union` getMetaVars lVarSet2

instance MetaVarContainer Law.VarContainer where
  getMetaVars (Law.VCTerm term) = getMetaVars term
  getMetaVars (Law.VCMetaVarContext metaC) = Set.singleton metaC
  getMetaVars (Law.VCMetaVarRed metaR) = Set.singleton metaR
  getMetaVars (Law.VCValueContext metaVctx) = Set.singleton metaVctx

instance MetaVarContainer Law.LetBindings where
  getMetaVars (Law.LBSBoth metaBindSet concreteLets) =
    let lawMVs = Set.unions $ map getMetaVars metaBindSet
        metasFromConcrete = Set.unions $ map getMetaVars concreteLets
    in lawMVs `Set.union` metasFromConcrete

instance MetaVarContainer Law.LetBinding where
  getMetaVars (Law.LBConcrete varMV sw hw lbterm) =
    Set.singleton varMV
      `Set.union` getMetaVars sw
      `Set.union` getMetaVars hw
      `Set.union` getMetaVars lbterm
  getMetaVars (Law.LBVectorized varVect1 sw hw varVect2) =
    Set.fromList [varVect1, varVect2]
      `Set.union` getMetaVars sw
      `Set.union` getMetaVars hw

instance MetaVarContainer Law.MetaBindSet where
  getMetaVars (Law.MBSMetaVar gamma) = Set.singleton gamma
  getMetaVars (Law.MBSSubstitution gamma x y) = Set.fromList [gamma, x, y]

instance MetaVarContainer Law.Reduction where
  getMetaVars (Law.RMetaVar metaR term) = Set.insert metaR $ getMetaVars term
  getMetaVars (Law.RApp term x) = Set.insert x $ getMetaVars term
  getMetaVars (Law.RPlusW term1 intExpr term2) =
    Set.unions [getMetaVars term1, getMetaVars intExpr, getMetaVars term2]
  getMetaVars (Law.RCase term branches) =
    getMetaVars term `Set.union` (Set.unions (map getMetaVars branches))
  getMetaVars (Law.RAddConst intExpr term) =
    getMetaVars intExpr `Set.union` getMetaVars term
  getMetaVars (Law.RIsZero term) = getMetaVars term
  getMetaVars (Law.RSeq term1 term2) =
    getMetaVars term1 `Set.union` getMetaVars term2

instance MetaVarContainer Law.CaseStm where
  getMetaVars (Law.CSAlts alts) = Set.singleton alts
  getMetaVars (Law.CSPatterns string term) =
    Set.insert string $ getMetaVars term
  getMetaVars (Law.CSConcrete (Law.CGeneral c xs) term) =
    Set.fromList [c,xs] `Set.union` getMetaVars term

instance MetaVarContainer Law.SideCond where
  getMetaVars Law.NoSideCond = Set.empty
  getMetaVars (Law.WithSideCond bt) = getMetaVars bt

instance MetaVarContainer Law.BoolTerm where
  getMetaVars (Law.BTSizeEq metaG1 metaG2) = Set.fromList [metaG1, metaG2]
  getMetaVars (Law.BTSetEq varSet1 varSet2) =
    getMetaVars varSet1 `Set.union` getMetaVars varSet2
  getMetaVars (Law.BTSubsetOf varSet1 varSet2) =
    getMetaVars varSet1 `Set.union` getMetaVars varSet2
  getMetaVars (Law.BTIn var varSet) =
    Set.insert var $ getMetaVars varSet
  getMetaVars (Law.BTNot boolTerm) = getMetaVars boolTerm
  getMetaVars (Law.BTLE intExpr1 intExpr2) =
    getMetaVars intExpr1 `Set.union` getMetaVars intExpr2
  getMetaVars (Law.BTGE intExpr1 intExpr2) =
    getMetaVars intExpr1 `Set.union` getMetaVars intExpr2
  getMetaVars (Law.BTGT intExpr1 intExpr2) =
    getMetaVars intExpr1 `Set.union` getMetaVars intExpr2
  getMetaVars (Law.BTIsFresh var) = Set.singleton var
  getMetaVars (Law.BTAreFresh xs) = Set.singleton xs
  getMetaVars (Law.BTReducesTo metaR metaV term) =
    Set.fromList [metaR, metaV] `Set.union` getMetaVars term
  getMetaVars (Law.BTAnd boolTerm1 boolTerm2) =
    getMetaVars boolTerm1 `Set.union` getMetaVars boolTerm2

-- | given M, returns the free variables of M.
getFreeVariables :: T.Term -> Set.Set String
getFreeVariables term = let (_, freeVars) = toLocallyNameless term
                        in freeVars

-- | Given a term, returns the set of all variable names used in that term,
-- regardless of if the variables are free or bound
getAllVariables :: T.Term -> Set.Set String
getAllVariables (T.TVar var) = Set.singleton var
getAllVariables (T.TLam var term) = Set.singleton var
                                      `Set.union` getAllVariables term
getAllVariables (T.TLet letBindings term) =
  getLBSVars letBindings `Set.union` getAllVariables term
  where
    getLBSVars = Set.unions . map getLBVars
    getLBVars :: (String, T.StackWeight, T.HeapWeight, T.Term) -> Set.Set String
    getLBVars (name, _sw, _hw, term) = let termSet = getAllVariables term
                                       in Set.insert name termSet
getAllVariables (T.TDummyBinds varSet term) = varSet
                                              `Set.union` getAllVariables term
getAllVariables (T.TRedWeight _ (T.RApp term var)) =
  let termSet = getAllVariables term
  in Set.insert var termSet
getAllVariables (T.TRedWeight _ (T.RCase term branches)) =
  let termSet = getAllVariables term
      (cNames, boundVars, terms) = unzip3 branches
      boundSet = Set.fromList $ concat boundVars
      termsSet = Set.unions $ map getAllVariables terms
  in Set.unions [termSet, boundSet, termsSet]
getAllVariables constructWithNoVariables =
  applyOnSubterms constructWithNoVariables Set.empty getAllVariables Set.unions

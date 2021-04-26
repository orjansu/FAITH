{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE LambdaCase #-}

module TermCorrectness where

import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified Data.Set as Set
import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import CheckMonad (assert, assertTerm)

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
    checkBoundVars term = case term of
      T.TVar var                 -> return ()
      T.TNum integer             -> return ()
      T.TLam var term            -> do
        checkBoundVar var
        checkBoundVars term
      T.THole                    -> return ()
      T.TLet letBindings term    -> do
        mapM checkBVLB letBindings
        checkBoundVars term
        where
          checkBVLB (name, sw, hw, term) = do
            checkBoundVar name
            checkBoundVars term
      T.TDummyBinds varSet term  -> checkBoundVars term
      T.TRedWeight redWeight red -> case red of
        T.RApp term var -> checkBoundVars term
        T.RPlusWeight t1 rw t2 -> do
          checkBoundVars t1
          checkBoundVars t2

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
getBoundVariables term = case term of
  T.TVar var -> Set.empty
  T.TNum integer -> Set.empty
  T.TLam var term -> Set.singleton var `Set.union` getBoundVariables term
  T.THole -> Set.empty
  T.TLet letBindings term -> boundVarsLBS `Set.union` getBoundVariables term
    where
      boundVarsLBS = Set.unions . map getLBBound $ letBindings
      getLBBound (var, _sw, _hw, term) =
        Set.singleton var `Set.union` getBoundVariables term
  T.TDummyBinds varSet term -> getBoundVariables term
  T.TRedWeight redWeight red -> case red of
    T.RApp term var -> getBoundVariables term
    T.RPlusWeight t1 rw t2 ->
      getBoundVariables t1 `Set.union` getBoundVariables t2

-- | Returns the number of holes in a term or context
numHoles :: T.Term -> Integer
numHoles (T.TVar _var) = 0
numHoles (T.TNum _integer) = 0
numHoles (T.TLam _var term) = numHoles term
numHoles (T.THole) = 1
numHoles (T.TLet letBindings term) = numHoles term + numHolesInLBS
  where
    numHolesInLBS = sum $ map numHolesInLB letBindings
    numHolesInLB (_var, _sw, _hw, term) = numHoles term
numHoles (T.TDummyBinds _varSet term) = numHoles term
numHoles (T.TRedWeight _redWeight red) = case red of
  T.RApp term _var -> numHoles term
  T.RPlusWeight t1 _rw t2 -> numHoles t1 + numHoles t2

isValue :: T.Term -> Bool
isValue (T.TVar _var) = False
isValue (T.TNum _integer) = True
isValue (T.TLam _var _term) = True
isValue (T.THole) = False
isValue (T.TLet _letBindings _term) = False
isValue (T.TDummyBinds _varSet term) = isValue term
isValue (T.TRedWeight _redWeight _redFD) = False

getAllMetaVars :: Law.Term -> Set.Set String
getAllMetaVars = \case
  Law.TValueMetaVar mvName -> Set.singleton mvName
  Law.TVar mvName -> Set.singleton mvName
  Law.TAppCtx mvName term ->
    Set.singleton mvName `Set.union` getAllMetaVars term
  Law.TLet letBindings term -> lbsMetas `Set.union` getAllMetaVars term
    where
      lbsMetas = case letBindings of
        Law.LBSBoth (Law.MBSMetaVar mv1) concreteLets ->
          let metasFromConcrete = Set.unions $ map concreteLBMetas concreteLets
          in Set.insert mv1 metasFromConcrete
      concreteLBMetas (varMV, sw, hw, lbterm) =
        Set.singleton varMV
          `Set.union` getIntExprMetas sw
          `Set.union` getIntExprMetas hw
          `Set.union` getAllMetaVars lbterm
  Law.TDummyBinds (Law.VSConcrete varSet) term ->
    varSet `Set.union` getAllMetaVars term
  where
    getIntExprMetas :: Law.IntExpr -> Set.Set String
    getIntExprMetas (Law.IEVar mv) = Set.singleton mv
    getIntExprMetas (Law.IENum _) = Set.empty

-- | given M, returns the free variables of M.
getFreeVariables :: T.Term -> Set.Set String
getFreeVariables term = let (_, freeVars) = toLocallyNameless term
                        in freeVars

-- | Given a term, returns the set of all variable names used in that term,
-- regardless of if the variables are free or bound
getAllVariables :: T.Term -> Set.Set String
getAllVariables (T.TVar var) = Set.singleton var
getAllVariables (T.TNum integer) = Set.empty
getAllVariables (T.TLam var term) = Set.singleton var
                                    `Set.union` getAllVariables term
getAllVariables (T.THole) = Set.empty
getAllVariables (T.TLet letBindings term) =
  getLBSVars letBindings `Set.union` getAllVariables term
  where
    getLBSVars = Set.unions . map getLBVars
    getLBVars :: (String, T.StackWeight, T.HeapWeight, T.Term) -> Set.Set String
    getLBVars (name, _sw, _hw, term) = let termSet = getAllVariables term
                                       in Set.insert name termSet
getAllVariables (T.TDummyBinds varSet term) = varSet
                                              `Set.union` getAllVariables term
getAllVariables (T.TRedWeight _redWeight red) =
  case red of
    T.RApp term var -> let termSet = getAllVariables term
                       in Set.insert var termSet
    T.RPlusWeight term1 _rw term2 ->
      getAllVariables term1 `Set.union` getAllVariables term2

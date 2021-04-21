{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module TermCorrectness where

import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified MiniTypedAST as T
import qualified Data.Set as Set

import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import OtherUtils (assert, assertTerm)

-- | given M and S, where S is the set of variables that are allowed to be free
-- in M, checks that:
-- - Does checks of checkFreeVars and checkBoundVariablesDistinct
-- - Checks that it is not a context
-- - Does not: Check typing of a simply typed lambda calculus
-- - General terms, i.e. any(M) are declared free (TODO)
checkTypedTerm :: (MonadError String m) => T.Term -> Set.Set String -> m ()
checkTypedTerm term expectedFreeVars = do
  checkBoundVariablesDistinct term
  checkFreeVars term expectedFreeVars
  assertTerm (numHoles term == 0)
    "Top-level terms should not be contexts" term

-- | given M, checks that the names of all bound variables in M are distinct.
--
-- Does not check anything else.
checkBoundVariablesDistinct :: (MonadError String m) => T.Term -> m ()
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
checkFreeVars :: (MonadError String m) => T.Term -> Set.Set String -> m ()
checkFreeVars term expectedFreeVars = do
  let (_lnlTerm, actualFreeVars) = toLocallyNameless term
  assert (expectedFreeVars `Set.isSubsetOf` actualFreeVars)
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

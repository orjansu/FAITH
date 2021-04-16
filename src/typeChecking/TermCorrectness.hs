{-# LANGUAGE FlexibleContexts #-}

module TermCorrectness where

import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified MiniTypedAST as T
import qualified Data.Set as Set

import ShowTypedTerm (showTypedTerm)

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

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Substitution (applySubstitution) where

import Data.Text (pack, Text)
import Data.List (intersperse)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import CheckMonad (CheckM, runCheckM, assert, assertInternal, internalException)
import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Except (MonadError, throwError)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables
                       , checkTypedTerm, numHoles, getAllVariables)
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import SubstitutionMonad (runSubstM, SubstM, getSubstitute, applyContext)

-- | Given M, sigma and S, where M is a law term with meta-
-- variables, sigma is a substitution that substitutes all meta-
-- variables for concrete variables and S is a set of variable names,
-- this function returns sigma applied to M, such that the names of the bound
-- variables in the result are unique, both with respect to the result term
-- and the variable names in S.
--
-- Fails if sigma doesn't contain substitutions for all meta-variables in M.
applySubstitution :: HasCallStack =>
                  Law.Term
                  -> T.Substitutions
                  -> Set.Set String
                  -> CheckM T.Term
applySubstitution law substitutions forbiddenNames1 = do
  Log.logInfoN . pack $ "applying substitution {"++showSubstitutions++"}"
  Log.logInfoN . pack $ "to law term"++show law
  Log.logInfoN . pack $ "With forbidden names "++ show forbiddenNames1
  -- TODO revise using SubstitutionMonad
  res <- runSubstM substitutions forbiddenNames1 $ applyTermSubstM law
  let (finalTerm, forbiddenNames2) = res
      finalBV = getBoundVariables finalTerm
  Log.logInfoN . pack $ "checking correctness of M after substitution , where "
    ++"M="++showTypedTerm finalTerm
  assertInternal (finalBV `Set.disjoint` forbiddenNames2) $ "The substituted "
    ++"term should not name the bound variables to forbidden names."
  checkBoundVariablesDistinct finalTerm
  assertInternal (numHoles finalTerm == 0) "| M should not be a context"
  let finalVariables = getAllVariables finalTerm
      expectedForbiddenNames = finalVariables `Set.union` forbiddenNames1
  assertInternal (expectedForbiddenNames == forbiddenNames2)
    "| M substituted wrt S -> S' => AllVars(M) union S == S'"
  return finalTerm
  where
    showSubstitutions = concat $
                          intersperse "," $
                            map showSingle $
                              Map.toList substitutions
    showSingle (name, subst) = name ++ " -> "++showSubstitute subst
    showSubstitute = \case
      T.SLetBindings letBindings ->
        showTypedTerm (T.TLet letBindings (T.TNum 1)) -- for now
      T.SValue term -> showTypedTerm term
      T.SContext term -> showTypedTerm term
      T.SIntegerVar intExpr -> case intExpr of
        T.IENum n -> show n
      T.SVar string -> string
      T.SVarSet stringSet ->
        let listForm = concat . intersperse ", " . Set.toList $ stringSet
        in "{" ++ listForm ++"}"
      T.STerm term -> showTypedTerm term

applyTermSubstM :: HasCallStack => Law.Term -> SubstM T.Term
applyTermSubstM = \case
  Law.TValueMetaVar mvName -> do
    T.SValue value <- getSubstitute mvName
    return value
  Law.TVar mvName -> do
    T.SVar var <- getSubstitute mvName
    return $ T.TVar var
  Law.TAppCtx mvName lawTerm -> do
    concreteTerm <- applyTermSubstM lawTerm
    applyContext mvName concreteTerm
  Law.TLet letBindings term -> do
    concreteTerm <- applyTermSubstM term
    concreteBindings <- applyOnLBS
    return $ T.TLet concreteBindings concreteTerm
      where
        applyOnLBS = case letBindings of
          Law.LBSBoth metaBinds moreConcreteBindings -> do
            case metaBinds of
              Law.MBSMetaVar metaBindVar -> do
                T.SLetBindings concreteFirst <- getSubstitute metaBindVar
                concreteRest <- mapM applyOnLB moreConcreteBindings
                let concrete = concreteFirst ++ concreteRest
                return concrete
        applyOnLB (Law.DLetBinding lawVar lawSw lawHw lawTerm) = do
          T.SVar var <- getSubstitute lawVar
          sw <- applyIntExprSubstM lawSw
          hw <- applyIntExprSubstM lawHw
          term <- applyTermSubstM lawTerm
          return (var, sw, hw, term)

  Law.TDummyBinds varSet term -> undefined

applyIntExprSubstM :: HasCallStack => Law.IntExpr -> SubstM Integer
applyIntExprSubstM = \case
  Law.IEVar var -> do
    T.SIntegerVar intExpr <- getSubstitute var
    case intExpr of
      T.IENum int -> return int
  Law.IENum num -> return num

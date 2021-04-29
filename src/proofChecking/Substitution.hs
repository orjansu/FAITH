{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Substitution (applySubstitution) where

import Data.Text (pack, Text)
import Data.List (intersperse, unzip4, zip4)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import CheckMonad (CheckM, runCheckM, assert, assertInternal, internalException)
import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Except (MonadError, throwError)
import Data.Foldable (foldlM)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables
                       , checkTypedTerm, numHoles, getAllVariables)
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import SubstitutionMonad (runSubstM, SubstM, getSubstitute, applyContext)
import ShowLaw (showLaw)

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
                  -> Set.Set String
                  -> CheckM T.Term
applySubstitution law substitutions forbiddenNames1 freeVars = do
  Log.logInfoN . pack $ "applying substitution {"++showSubstitutions++"}"
  Log.logInfoN . pack $ "to law term"++showLaw law
  Log.logInfoN . pack $ "With forbidden names "++ show forbiddenNames1
  let boundSubstVars = getBoundSubstVars substitutions law
      forbiddenNames2 = forbiddenNames1 `Set.union` boundSubstVars
  checkSubstBVDistinct substitutions forbiddenNames2
  res <- runSubstM substitutions forbiddenNames2 $ applyTermSubstM law
  let (finalTerm, forbiddenNames3) = res
      finalBV = getBoundVariables finalTerm
  Log.logInfoN . pack $ "checking correctness of M after substitution , where "
    ++"M="++showTypedTerm finalTerm
  checkTypedTerm finalTerm freeVars
  assertInternal (finalBV `Set.disjoint` forbiddenNames1) $ "The substituted "
    ++"term should not name the bound variables to forbidden names. \n"
    ++"Bound variables are: "++show finalBV
  assertInternal (numHoles finalTerm == 0) "| M should not be a context"
  let finalVariables = getAllVariables finalTerm
      expectedForbiddenNames = finalVariables `Set.union` forbiddenNames1
  assertInternal (expectedForbiddenNames == forbiddenNames3)
    $ "| M substituted wrt S -> S' => AllVars(M) union S == S', where "
    ++"AllVars(M) union S = "++show expectedForbiddenNames++" and "
    ++"S' = "++show forbiddenNames3

  return finalTerm
  where
    showSubstitutions = concat $
                          intersperse "," $
                            map showSingle $
                              Map.toList substitutions
    showSingle (name, subst) = name ++ " -> "++showSubstitute subst
    showSubstitute = \case
      T.SLetBindings letBindings ->
        showTypedTerm letBindings
      T.SValue term -> showTypedTerm term
      T.SContext term -> showTypedTerm term
      T.SIntegerVar intExpr -> show intExpr
      T.SVar string -> string
      T.SVarSet stringSet ->
        let listForm = concat . intersperse ", " . Set.toList $ stringSet
        in "{" ++ listForm ++"}"
      T.STerm term -> showTypedTerm term

-- | Checks that none of the substitutions has a bound variable that
-- has a name that is forbidden (in the forbidden names) or that one bound
-- variable in one substitution has the same name as a bound variable in
-- another substitution.
checkSubstBVDistinct :: T.Substitutions -> Set.Set String -> CheckM [()]
checkSubstBVDistinct substitutions forbiddenNames = do
  Log.logInfoN . pack $ "Checking that the names of the bound variables in the "
    ++"substitutions are valid (i.e. distinct from each other and the free "
    ++"variables)."
  (flip evalStateT) forbiddenNames $
    mapM checkBVSubstitution $ Map.elems substitutions
  where
    checkBVSubstitution :: T.Substitute -> StateT (Set.Set String) CheckM ()
    checkBVSubstitution = \case
      T.SLetBindings letBindings -> do
        let (bindVars, _sw, _hw, terms) = unzip4 letBindings
            innerBVs = map getBoundVariables terms
            bindVarSet = Set.fromList bindVars
        forbiddenNames1 <- get
        let shouldBeDistinct = forbiddenNames1:bindVarSet:innerBVs
        forbiddenNames2 <- assertDisjointAndMerge shouldBeDistinct
        put forbiddenNames2
      T.SValue term -> checkBVTerm term
      T.SContext term -> checkBVTerm term
      T.SIntegerVar intExpr -> return ()
      T.SVar string -> return ()
      T.SVarSet varSet -> return ()
      T.STerm term -> checkBVTerm term

    checkBVTerm :: T.Term -> StateT (Set.Set String) CheckM ()
    checkBVTerm term = do
      let bvSet = getBoundVariables term
      forbiddenNames1 <- get
      forbiddenNames2 <- assertDisjointAndMerge [bvSet, forbiddenNames1]
      put forbiddenNames2

    -- | asserts that every set in the list is disjoint from all other sets in
    -- the list.
    assertDisjointAndMerge :: (MonadError String m, Log.MonadLogger m,
                              HasCallStack, Ord a, Show a) =>
                      [Set.Set a] -> m (Set.Set a)
    assertDisjointAndMerge sets = do
      foldlM assertMerge2 Set.empty sets
      where
        assertMerge2 :: (MonadError String m, Log.MonadLogger m,
                               HasCallStack, Ord a, Show a) =>
                               Set.Set a -> Set.Set a -> m (Set.Set a)
        assertMerge2 set1 set2 = do
          assert (set1 `Set.disjoint` set2) $ "The variable(s) "
            ++show (set1 `Set.intersection` set2)++" should not be used in "
            ++"multiple bindings and should be distinct from the free "
            ++"variables."
          return $ set1 `Set.union` set2


-- | returns the variables that are substituted into a binding position.
getBoundSubstVars :: T.Substitutions -> Law.Term -> Set.Set String
getBoundSubstVars substitutions law = case law of
  Law.TValueMetaVar _ -> Set.empty
  Law.TVar _ -> Set.empty
  Law.TAppCtx _ term -> getBoundSubstVars substitutions term
  Law.TLet letBindings term ->
    let mainBounds = getBoundSubstVars substitutions term
    in mainBounds `Set.union` innerBounds
    where
      innerBounds = case letBindings of
        -- It only makes sense to substitute bound varibles, so even though
        -- metaBinds may contain a substitution, that substitution is not
        -- allowed to be on a variable in a binding position. Therefore, we
        -- can ignore _MetaBinds.
        Law.LBSBoth _MetaBinds innerLetbinds ->
          Set.unions $ map getLBBound innerLetbinds
      getLBBound :: Law.LetBinding -> Set.Set String
      getLBBound (lawVar, _, _, term) =
        case Map.lookup lawVar substitutions of
          Just (T.SVar substVar) ->
            let otherBoundVars = getBoundSubstVars substitutions term
            in Set.insert substVar otherBoundVars
          _ -> error $ "Internal: substitution for"++lawVar++" is not bound to "
                       ++"a variable. This was not discovered in the "
                       ++"typechecker."
  Law.TDummyBinds _ term -> getBoundSubstVars substitutions term

applyTermSubstM :: HasCallStack => Law.Term -> SubstM T.Term
applyTermSubstM bigLawTerm = do
  Log.logInfoN . pack $ "substituting into law "++showLaw bigLawTerm
  case bigLawTerm of
    Law.TValueMetaVar mvName -> do
      T.SValue value <- getSubstitute mvName
      logSubst mvName value
      return value
    Law.TVar mvName -> do
      T.SVar var <- getSubstitute mvName
      logSubst mvName $ T.TVar var
      return $ T.TVar var
    Law.TAppCtx mvName lawTerm -> do
      concreteTerm <- applyTermSubstM lawTerm
      Log.logInfoN . pack $ "applying context "++mvName
        ++" to "++showTypedTerm concreteTerm
      applyContext mvName concreteTerm
    Law.TLet letBindings term -> do
      concreteBindings <- applyOnLBS
      concreteTerm <- applyTermSubstM term
      return $ T.TLet concreteBindings concreteTerm
        where
          applyOnLBS = case letBindings of
            Law.LBSBoth metaBinds moreConcreteBindings -> do
              concreteFirsts <- mapM applyMBS metaBinds
              concreteRest <- mapM applyOnLB moreConcreteBindings
              let concrete = concat concreteFirsts ++ concreteRest
              return concrete
          applyMBS (Law.MBSMetaVar metaBindVar) = do
              T.SLetBindings concreteFirst <- getSubstitute metaBindVar
              return concreteFirst
          applyOnLB (lawVar, lawSw, lawHw, lawTerm) = do
            T.SVar var <- getSubstitute lawVar
            sw <- applyIntExprSubstM lawSw
            hw <- applyIntExprSubstM lawHw
            term <- applyTermSubstM lawTerm
            return (var, sw, hw, term)
    Law.TDummyBinds (Law.VSConcrete lawVarSet) lawTerm -> do
      concreteWrappedVarList <- mapM getSubstitute $ Set.toList lawVarSet
      let concreteVarList = map (\(T.SVar str) -> str) concreteWrappedVarList
          varSet = Set.fromList concreteVarList
      term <- applyTermSubstM lawTerm
      return $ T.TDummyBinds varSet term
  where
    logSubst mvName term = Log.logInfoN . pack $ "applying substitution "
                            ++mvName++" = "++showTypedTerm term

applyIntExprSubstM :: HasCallStack => Law.IntExpr -> SubstM Integer
applyIntExprSubstM = \case
  Law.IEVar var -> do
    T.SIntegerVar int <- getSubstitute var
    return int
  Law.IENum num -> return num

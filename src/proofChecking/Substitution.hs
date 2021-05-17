{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Substitution (applySubstitution, checkSideCondition, substituteFor) where

import Data.Text (pack, Text)
import Data.List (intersperse, unzip4, zip4)
import Maybes (firstJust, firstJusts)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Except (MonadError, throwError)

import CheckMonad (CheckM, runCheckM, assert, assertInternal, internalException)
import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables
         , checkTypedTerm, numHoles, getAllVariables, getFreeVariables)
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import SubstitutionMonad (runSubstM, SubstM, getSubstitute, applyContext
                          , getCtxFreeVars, isFresh, liftCheckM)
import ShowLaw (showLaw)
import OtherUtils (applyOnLawSubterms, applyOnLawSubtermsM, applyAndRebuild)
import LanguageLogic (reduce)
import TermUtils (substituteFor, isAlphaEquiv, showSubstitute)

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
                  -> Law.SideCond
                  -> T.Substitutions
                  -> Set.Set String
                  -> Set.Set String
                  -> CheckM T.Term
applySubstitution law sideCond substitutions forbiddenNames1 freeVars = do
  Log.logInfoN . pack $ "applying substitution {"++showSubstitutions++"}"
  Log.logInfoN . pack $ "to law term"++showLaw law
  Log.logInfoN . pack $ "With forbidden names "++ show forbiddenNames1
  let boundSubstVars = getBoundSubstVars substitutions law
      freshVars = getFreshVariables substitutions sideCond
      forbiddenNames2 = forbiddenNames1
                          `Set.union` boundSubstVars
                          `Set.union` freshVars
  res <- runSubstM substitutions forbiddenNames2 $ applyTermSubstM (-1) law
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
  --assertInternal (expectedForbiddenNames == forbiddenNames3)
  --  $ "| M substituted wrt S -> S' => AllVars(M) union S == S', where "
  --  ++"AllVars(M) union S = "++show expectedForbiddenNames++" and "
  --  ++"S' = "++show forbiddenNames3
  --TODO: change to a better assertion, since things will be renamed in vain
  --      when you get terms for getting their free variables.
  return finalTerm
  where
    showSubstitutions = concat $
                          intersperse "," $
                            map showSingle $
                              Map.toList substitutions
    showSingle (name, subst) = name ++ " -> "++showSubstitute subst
-- | Given a sidecondition and a set of substitutions (where all substitutions
-- for the sidecondition are provided), the function checks if the
-- sideconditions hold. NOTE: since the only involvement of terms in the side-
-- conditions concern the names of variables in let-bindings and the names of
-- free variables, this function does not have to take into account the bound
-- variables and doesn't have to make sure that bound variables do not clash.
-- therefore, no forbidden names are provided, and the set of forbidden names
-- given to the substitution monad is empty for this reason. If this function
-- is expanded to include conditions that also concern the bound variables in
-- some way, this function (and possibly much else of the general approach)
-- would need to be revised.
checkSideCondition :: HasCallStack =>
                      Law.SideCond
                      -> T.Substitutions
                      -> Set.Set String
                      -> CheckM ()
checkSideCondition Law.NoSideCond _ _ = return ()
checkSideCondition (Law.WithSideCond boolTerm) substitutions forbiddenNames = do
  (res, _fv) <- runSubstM substitutions forbiddenNames $ evalBoolTerm boolTerm
  assert (res == True) "The sideconditions must hold."

getFreshVariables :: HasCallStack =>
                     T.Substitutions -> Law.SideCond -> Set.Set String
getFreshVariables _ Law.NoSideCond = Set.empty
getFreshVariables subst (Law.WithSideCond sideCond) = go sideCond
  where
  go (Law.BTSizeEq _ _) = Set.empty
  go (Law.BTSetEq _ _) = Set.empty
  go (Law.BTSubsetOf _ _) = Set.empty
  go (Law.BTIn _ _) = Set.empty
  go (Law.BTNot lBoolTerm) =
    let fresh = go lBoolTerm
    in if fresh == Set.empty
        then Set.empty
        else error $ "not (... is fresh ...) and not (... are fresh ...) is "
          ++"not supported and got all the way to substitution."
  go (Law.BTLE _ _) = Set.empty
  go (Law.BTGE _ _) = Set.empty
  go (Law.BTGT _ _) = Set.empty
  go (Law.BTIsFresh lVar) = case Map.lookup lVar subst of
    Just (T.SVar cVar) -> Set.singleton cVar
    _ -> error $ "substitution for "++lVar++" not provided."
  go (Law.BTAreFresh lVars) = case Map.lookup lVars subst of
    Just (T.SVarVect cVars) -> Set.fromList cVars
    _ -> error $ "substitution for "++lVars++" not provided."
  go (Law.BTReducesTo _ _ _) = Set.empty
  go (Law.BTAnd lBoolTerm1 lBoolTerm2) =
    go lBoolTerm1 `Set.union` go lBoolTerm2

-- | returns the variables that are substituted into a binding position,
-- including possible binding vars in M in terms like {FV(M)}d^N.
-- NOTE: unclear if the binding pos variables in M in {FV(M)}d^N are needed.
-- maybe add typechecker check that if {FV(M)}d^N appears, M must also appear
-- somewhere else?
getBoundSubstVars :: HasCallStack =>
                     T.Substitutions -> Law.Term -> Set.Set String
getBoundSubstVars substitutions law = case law of
  Law.TDummyBinds vs term ->
    getBoundSubstVars substitutions term `Set.union` inVarSet vs
    where
      inVarSet (Law.VSConcrete _) = Set.empty
      inVarSet (Law.VSMetaVar _) = Set.empty
      inVarSet (Law.VSVectMeta _) = Set.empty
      inVarSet (Law.VSFreeVars vc) = case vc of
        Law.VCTerm term -> getBoundSubstVars substitutions term
        Law.VCMetaVarContext _ -> Set.empty
        Law.VCMetaVarRed _ -> Set.empty
        Law.VCValueContext _ -> Set.empty
      inVarSet (Law.VSDomain _) = Set.empty
      inVarSet (Law.VSUnion varSet1 varSet2) =
        inVarSet varSet1 `Set.union` inVarSet varSet2
      inVarSet (Law.VSDifference varSet1 varSet2) =
        inVarSet varSet1 `Set.union` inVarSet varSet2
  Law.TLam lawVar term -> case Map.lookup lawVar substitutions of
    Just (T.SVar var) -> Set.singleton var
                  `Set.union` getBoundSubstVars substitutions term
    _ -> substitutionNotfound lawVar
  Law.TRedWeight _ (Law.RCase decTerm cases) -> bvDecTerm `Set.union` bvCases
    where
      bvDecTerm = getBoundSubstVars substitutions decTerm
      bvCases = Set.unions $ map bvCase cases
      bvCase (Law.CSAlts _) = Set.empty
      bvCase (Law.CSPatterns pat_i term) =
        case Map.lookup pat_i substitutions of
          Just (T.SPatterns patterns) ->
            let (constructors, argss) = unzip patterns
                argsBVs = Set.fromList $ concat argss
            in argsBVs `Set.union` getBoundSubstVars substitutions term
          _ -> substitutionNotfound pat_i
      bvCase (Law.CSConcrete (Law.CGeneral _name lawArgs) term) =
        case Map.lookup lawArgs substitutions of
          Just (T.SVarVect args) -> Set.fromList args
            `Set.union` getBoundSubstVars substitutions term
          _ -> substitutionNotfound lawArgs
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
      getLBBound :: HasCallStack => Law.LetBinding -> Set.Set String
      getLBBound (Law.LBConcrete lawVar _ _ term) =
        case Map.lookup lawVar substitutions of
          Just (T.SVar substVar) ->
            let otherBoundVars = getBoundSubstVars substitutions term
            in Set.insert substVar otherBoundVars
          _ -> substitutionNotfound lawVar
      getLBBound (Law.LBVectorized varVect1 sw hw varVect2) =
        let lookup1 = Map.lookup varVect1 substitutions
            lookup2 = Map.lookup varVect2 substitutions
        in case (lookup1, lookup2) of
            (Just (T.SVarVect vars1), Just (T.SVarVect vars2)) ->
              Set.fromList (vars1 ++ vars2)
            _ -> substitutionNotfound $ varVect1++" and/or "++varVect2
  nonBindingTerm -> applyOnLawSubterms law
                                       Set.empty
                                       (getBoundSubstVars substitutions)
                                       Set.unions
  where
    substitutionNotfound lawVar = error $
                   "Internal: substitution for"++lawVar++" is not bound to "
                 ++"a variable. This was not discovered in the "
                 ++"typechecker."


-- | Applies a substitution to a law term.
-- TODO: check that you do not substitute into a binding position.
applyTermSubstM :: HasCallStack => Int -> Law.Term -> SubstM T.Term
applyTermSubstM index bigLawTerm = do
  Log.logInfoN . pack $ "substituting into law "++showLaw bigLawTerm
  case bigLawTerm of
    Law.TValueMetaVar mvName -> do
      T.SValue value <- getSubstitute mvName
      return value
    Law.TGeneralMetaVar mvName -> do
      T.STerm term <- getSubstitute mvName
      return term
    Law.TMVTerms mvName -> do
      assertInternal (index /= (-1)) $
        "Index should be set when vectorized term "++mvName++" is used."
      T.STerms terms <- getSubstitute mvName
      let term = terms !! index
      return term
    Law.TVar mvName -> do
      T.SVar var <- getSubstitute mvName
      return $ T.TVar var
    Law.TAppCtx mvName lawTerm -> do
      concreteTerm <- applyTermSubstM index lawTerm
      applyContext mvName concreteTerm
    Law.TAppValCtx mvName lawTerm -> do
      concreteTerm <- applyTermSubstM index lawTerm
      applyContext mvName concreteTerm
    Law.TNonTerminating -> return T.TNonTerminating
    Law.TNum int -> return $ T.TNum int
    Law.TConstructor (Law.CGeneral lname largs) -> do
      T.SConstructorName cname <- getSubstitute lname
      T.SVarVect cargs <- getSubstitute largs
      return $ T.TConstructor cname cargs
    Law.TStackSpikes iexpr lterm -> do
      res <- substituteAndEvalIntExpr iexpr
      cterm <- applyTermSubstM index lterm
      return $ T.TStackSpikes res cterm
    Law.THeapSpikes iexpr lterm -> do
      res <- substituteAndEvalIntExpr iexpr
      cterm <- applyTermSubstM index lterm
      return $ T.THeapSpikes res cterm
    Law.TDummyBinds lvarSet lawTerm -> do
      varSet <- substituteAndEvalVarSet index lvarSet
      term <- applyTermSubstM index lawTerm
      return $ T.TDummyBinds varSet term
    Law.TSubstitution lterm ly lx -> do
      -- M[y/x]
      term <- applyTermSubstM index lterm
      T.SVar y <- getSubstitute ly
      T.SVar x <- getSubstitute lx
      substitutedTerm <- substituteFor term y x
      return substitutedTerm
    Law.TLam lawVar lawTerm -> do
      T.SVar var <- getSubstitute lawVar
      term <- applyTermSubstM index lawTerm
      return $ T.TLam var term
    Law.TLet letBindings term -> do
      concreteBindings <- applyOnLBS
      concreteTerm <- applyTermSubstM index term
      return $ T.TLet concreteBindings concreteTerm
        where
          applyOnLBS = case letBindings of
            Law.LBSBoth metaBinds moreConcreteBindings -> do
              concreteFirsts <- mapM applyMBS metaBinds
              concreteRest <- mapM applyOnLB moreConcreteBindings
              let concrete = concat (concreteFirsts ++ concreteRest)
              return concrete
          applyMBS (Law.MBSMetaVar metaBindVar) = do
            T.SLetBindings concreteFirst <- getSubstitute metaBindVar
            return concreteFirst
          applyMBS (Law.MBSSubstitution metaG y x) = do
            T.SLetBindings concreteG <- getSubstitute metaG
            let dummyTerm = T.TLet concreteG (T.TNum 1)
            T.TLet substitutedG (T.TNum 1) <- substituteFor dummyTerm y x
            return substitutedG
          applyOnLB (Law.LBConcrete lawVar lawSw lawHw lawTerm) = do
            T.SVar var <- getSubstitute lawVar
            sw <- substituteAndEvalIntExpr lawSw
            hw <- substituteAndEvalIntExpr lawHw
            term <- applyTermSubstM index lawTerm
            return [(var, sw, hw, term)]
          applyOnLB (Law.LBVectorized varVect1 lawSw lawHw varVect2) = do
            T.SVarVect vars1 <- getSubstitute varVect1
            T.SVarVect vars2 <- getSubstitute varVect2
            sw <- substituteAndEvalIntExpr lawSw
            hw <- substituteAndEvalIntExpr lawHw
            let toBinding = (\(x, y) -> (x, sw, hw, T.TVar y))
                bindings = map toBinding $ zip vars1 vars2
            return bindings
    Law.TRedWeight lrw lred -> do
      rw <- substituteAndEvalIntExpr lrw
      red <- substRed lred
      return $ T.TRedWeight rw red
      where
        substRed (Law.RMetaVar lReduction lTerm) = do
          term <- applyTermSubstM index lTerm
          T.TRedWeight 1 reduction <- applyContext lReduction term
          return reduction
        substRed (Law.RApp lterm lvar) = do
          term <- applyTermSubstM index lterm
          T.SVar var <- getSubstitute lvar
          return $ T.RApp term var
        substRed (Law.RPlusW lTerm1 lrw2 lTerm2) = do
          term1 <- applyTermSubstM index lTerm1
          rw2 <- substituteAndEvalIntExpr lrw2
          term2 <- applyTermSubstM index lTerm2
          return $ T.RPlusWeight term1 rw2 term2
        substRed (Law.RCase lterm lbranches) = do
          term <- applyTermSubstM index lterm
          unConcatBranches <- mapM applyBranch lbranches
          let branches = concat unConcatBranches
          return $ T.RCase term branches
          where
            applyBranch (Law.CSAlts alts) = do
              T.SCaseStms concreteAlts <- getSubstitute alts
              return concreteAlts
            applyBranch (Law.CSPatterns pat_i lterm) = do
              T.SPatterns patterns <- getSubstitute pat_i
              let indicies = [0..length patterns - 1]
                  applyTupled = (\(i,t) -> applyTermSubstM i t)
              terms <- mapM applyTupled $ zip indicies $ repeat lterm
              let (constrNames, args) = unzip patterns
                  branches = zip3 constrNames args terms
              return branches
            applyBranch (Law.CSConcrete (Law.CGeneral lc lxs) lM) = do
              T.SConstructorName c <- getSubstitute lc
              T.SVarVect xs <- getSubstitute lxs
              m <- applyTermSubstM index lM
              return [(c,xs,m)]
        substRed (Law.RAddConst ln lM) = do
          n <- substituteAndEvalIntExpr ln
          m <- applyTermSubstM index lM
          return $ T.RAddConst n m
        substRed (Law.RIsZero lTerm) = do
          term <- applyTermSubstM index lTerm
          return $ T.RIsZero term
        substRed (Law.RSeq lTerm1 lTerm2) = do
          term1 <- applyTermSubstM index lTerm1
          term2 <- applyTermSubstM index lTerm2
          return $ T.RSeq term1 term2

substituteAndEvalIntExpr :: HasCallStack => Law.IntExpr -> SubstM Integer
substituteAndEvalIntExpr = \case
  Law.IEVar var -> do
    T.SIntegerVar int <- getSubstitute var
    return int
  Law.IENum num -> return num
  Law.IESizeBind metaG -> do
    T.SLetBindings concreteG <- getSubstitute metaG
    return $ toInteger $ length concreteG
  Law.IEPlus ie1 ie2 -> do
    m <- substituteAndEvalIntExpr ie1
    n <- substituteAndEvalIntExpr ie2
    return $ m + n
  Law.IEMinus ie1 ie2 -> do
    m <- substituteAndEvalIntExpr ie1
    n <- substituteAndEvalIntExpr ie2
    return $ m - n

substituteAndEvalVarSet :: HasCallStack =>
                           Int -> Law.VarSet -> SubstM (Set.Set String)
substituteAndEvalVarSet index law = case law of
  Law.VSConcrete lawVarSet -> do
    concreteWrappedVarList <- mapM getSubstitute $ Set.toList lawVarSet
    let concreteVarList = map (\(T.SVar str) -> str) concreteWrappedVarList
        varSet = Set.fromList concreteVarList
    return varSet
  Law.VSMetaVar metaX -> do
    T.SVarSet concreteX <- getSubstitute metaX
    return concreteX
  Law.VSVectMeta metaxs -> do
    T.SVarVect concretexs <- getSubstitute metaxs
    return $ Set.fromList $ concretexs
  Law.VSFreeVars varContainer -> case varContainer of
    Law.VCTerm lterm -> do
      term <- applyTermSubstM index lterm
      return $ getFreeVariables term
    Law.VCMetaVarContext metaC -> getCtxFreeVars metaC
    Law.VCMetaVarRed metaR -> getCtxFreeVars metaR
    Law.VCValueContext metaV -> getCtxFreeVars metaV
  Law.VSDomain metaG -> do
    T.SLetBindings concreteG <- getSubstitute metaG
    let (bindVars, _,_,_) = unzip4 concreteG
    return $ Set.fromList bindVars
  Law.VSUnion lVarSet1 lVarSet2 -> do
    varSet1 <- substituteAndEvalVarSet index lVarSet1
    varSet2 <- substituteAndEvalVarSet index lVarSet2
    return $ varSet1 `Set.union` varSet2
  Law.VSDifference lVarSet1 lVarSet2 -> do
    varSet1 <- substituteAndEvalVarSet index lVarSet1
    varSet2 <- substituteAndEvalVarSet index lVarSet2
    return $ varSet1 Set.\\ varSet2

-- | NOTE: The correctness of the  implementation of BTIsFresh and BTAreFresh
-- depends on that all the fresh variables are added to the set of forbidden
-- names before substitution into the law term (see the use of
-- getFreshVariables in applySubstitution) and that all substitutions are
-- provided (see check in the typechecker).
evalBoolTerm :: HasCallStack => Law.BoolTerm -> SubstM Bool
evalBoolTerm (Law.BTSizeEq metaG1 metaG2) = do
  T.SLetBindings concreteG1 <- getSubstitute metaG1
  T.SLetBindings concreteG2 <- getSubstitute metaG2
  return $ length concreteG1 == length concreteG2
evalBoolTerm (Law.BTSetEq lVarSet1 lVarSet2) = do
  cVarSet1 <- evalPossiblyVectorizedVarSet lVarSet1
  cVarSet2 <- evalPossiblyVectorizedVarSet lVarSet2
  return $ cVarSet1 == cVarSet2
evalBoolTerm (Law.BTSubsetOf varSet1 varSet2) = do
  cVarSet1 <- evalPossiblyVectorizedVarSet varSet1
  cVarSet2 <- evalPossiblyVectorizedVarSet varSet2
  return $ cVarSet1 `Set.isSubsetOf` cVarSet2
evalBoolTerm (Law.BTIn lVar lVarSet) = do
  T.SVar cVar <- getSubstitute lVar
  cVarSet <- evalPossiblyVectorizedVarSet lVarSet
  return $ cVar `Set.member` cVarSet
evalBoolTerm (Law.BTNot lBoolTerm) = do
  cBoolTerm <- evalBoolTerm lBoolTerm
  return $ not cBoolTerm
evalBoolTerm (Law.BTLE lIntExpr1 lIntExpr2) = do
  res1 <- substituteAndEvalIntExpr lIntExpr1
  res2 <- substituteAndEvalIntExpr lIntExpr2
  return $ res1 <= res2
evalBoolTerm (Law.BTGE lIntExpr1 lIntExpr2) = do
  res1 <- substituteAndEvalIntExpr lIntExpr1
  res2 <- substituteAndEvalIntExpr lIntExpr2
  return $ res1 >= res2
evalBoolTerm (Law.BTGT lIntExpr1 lIntExpr2) = do
  res1 <- substituteAndEvalIntExpr lIntExpr1
  res2 <- substituteAndEvalIntExpr lIntExpr2
  return $ res1 > res2
evalBoolTerm (Law.BTIsFresh x) = isFresh x
evalBoolTerm (Law.BTAreFresh xs) = isFresh xs
evalBoolTerm (Law.BTReducesTo lReductionStr lValueStr lTerm) = do
  T.SValue value <- getSubstitute lValueStr
  substituted <- applyContext lReductionStr value
  Log.logInfoN . pack $ "reducing R[V]="
    ++showTypedTerm substituted
  result <- reduce substituted
  tTerm <- applyTermSubstM (-1) lTerm
  liftCheckM $ result `isAlphaEquiv` tTerm
evalBoolTerm (Law.BTAnd lBoolTerm1 lBoolTerm2) = do
  b1 <- evalBoolTerm lBoolTerm1
  b2 <- evalBoolTerm lBoolTerm2
  return $ b1 && b2

evalPossiblyVectorizedVarSet :: HasCallStack =>
                                Law.VarSet -> SubstM (Set.Set String)
evalPossiblyVectorizedVarSet lVarSet = case lVarSet of
  Law.VSConcrete _ -> substituteAndEvalVarSet (-1) lVarSet
  Law.VSMetaVar _ -> substituteAndEvalVarSet (-1) lVarSet
  Law.VSVectMeta _ -> substituteAndEvalVarSet (-1) lVarSet
  Law.VSFreeVars varContainer -> case varContainer of
    Law.VCTerm term -> do
      lenIfVect <- getLenIfVectorized term
      case lenIfVect of
        Just len -> do
          let tupledEval = (\(i,vs) -> substituteAndEvalVarSet i vs)
          sets <- mapM tupledEval $ zip [0..len-1] $ repeat lVarSet
          return $ Set.unions sets
        Nothing -> substituteAndEvalVarSet (-1) lVarSet
      where
        getLenIfVectorized :: HasCallStack => Law.Term -> SubstM (Maybe Int)
        getLenIfVectorized = \case
          Law.TMVTerms metaN_i -> do
            T.STerms concreteN_i <- getSubstitute metaN_i
            return $ Just $ length concreteN_i
          Law.TDummyBinds (Law.VSFreeVars (Law.VCTerm fvTerm)) term -> do
            mlfvt <- getLenIfVectorized fvTerm
            mlt <- getLenIfVectorized term
            return $ firstJust mlfvt mlt
          otherTerm -> applyOnLawSubtermsM otherTerm
                                           Nothing
                                           getLenIfVectorized
                                           firstJusts

    Law.VCMetaVarContext _ -> substituteAndEvalVarSet (-1) lVarSet
    Law.VCMetaVarRed _ -> substituteAndEvalVarSet (-1) lVarSet
    Law.VCValueContext _ -> substituteAndEvalVarSet (-1) lVarSet
  Law.VSDomain _ -> substituteAndEvalVarSet (-1) lVarSet
  Law.VSUnion lVarSet1 lVarSet2 -> do
    cVarSet1 <- evalPossiblyVectorizedVarSet lVarSet1
    cVarSet2 <- evalPossiblyVectorizedVarSet lVarSet2
    return $ cVarSet1 `Set.union` cVarSet2
  Law.VSDifference lVarSet1 lVarSet2 -> do
    cVarSet1 <- evalPossiblyVectorizedVarSet lVarSet1
    cVarSet2 <- evalPossiblyVectorizedVarSet lVarSet2
    return $ cVarSet1 Set.\\ cVarSet2

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module ProofChecker where

import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import qualified Data.Map.Strict as Map
import Data.Text (pack, Text)
import Data.List (permutations, intersperse, zip4, unzip4)
import qualified Data.Set as Set

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import qualified LanguageLogic as Lang
import qualified Common as Com (ImpRel(..))
import ToLocallyNameless (toLocallyNameless)
import qualified LocallyNameless as LNL
import ToPrettyLNL (showLNL)
import ShowTypedTerm (showTypedTerm)
import CheckMonad (CheckM, runCheckM, assert, assertInternal
                  , throwCallstackError)
import Substitution (applySubstitution, checkSideCondition)
import OtherUtils (applyOnLawSubterms)
import TermUtils (isAlphaEquiv, computeDifference)

import Debug.Trace (trace)

-- | Checks whether a detailed proof script is correct. Returns a [String],
-- containing a log and error message if it is incorrect, and Nothing
-- if it is correct.
--
-- Assumes that the incoming proof script is typechecked.
checkDetailedProof :: HasCallStack => T.ProofScript -> Maybe [String]
checkDetailedProof proofScript =
  case runCheckM $ check proofScript of
    Right () -> Nothing
    Left errorMsgs -> Just errorMsgs

class Checkable a where
  check :: HasCallStack => a -> CheckM ()

instance Checkable T.ProofScript where
  check (T.DProofScript theorems) = mapM check theorems >> return ()

instance Checkable T.Theorem where
  check (T.DTheorem (T.DProposition freeVars start imprel goal) proof) = do
    checkProofSteps proof start imprel freeVars goal

type GlobalImpRel = Com.ImpRel
type Start = T.Term
type Goal = T.Term

checkProofSteps :: HasCallStack =>
                    T.Proof
                   -> Start
                   -> GlobalImpRel
                   -> T.FreeVars
                   -> Goal
                   -> CheckM ()
checkProofSteps (T.Simple proofSteps) start globalImpRel freeVars goal = do
  let (T.PSMiddle startTerm _ _ _) = head proofSteps
  checkAlphaEqWrtLetReorder start startTerm
  mapM (checkStep globalImpRel freeVars) proofSteps
  let (T.PSMiddle _ _ _ endTerm) = last proofSteps
  checkAlphaEqWrtLetReorder goal endTerm

-- | Checks if a single step is valid. This computation may be run
-- independently in parallel for each step to speed things up if that is an
-- issue. Could maybe use the globally free variables to speed things up later.
checkStep :: HasCallStack =>
             GlobalImpRel -> T.FreeVars -> T.ProofStep -> CheckM ()
checkStep globalImpRel
          (T.DFreeVars termFreeVars varFreeVars)
          (T.PSMiddle term1 command localImpRel term2) = do
  Log.logInfoN . pack $ "checking that "++showTypedTerm term1++" "
  Log.logInfoN . pack $ show localImpRel
  Log.logInfoN . pack $ showTypedTerm term2
  Log.logInfoN . pack $ "using the law "++show command
  Log.logInfoN . pack $ "with the global improvement relation being "
    ++show globalImpRel
  assert (localImpRel `Lang.impRelImplies` globalImpRel)
    $ show localImpRel ++ " should imply "++ show globalImpRel
  case command of
    T.AlphaEquiv -> checkAlphaEqWrtLetReorder term1 term2
    T.Law context
          (Law.DLaw lawName lawLHS lawImpRel lawRHS sideCond)
          substitutions -> do
      assert (lawImpRel == localImpRel)
        $ "The improvement relation of the law ("++show localImpRel++")"
        ++ "must be the same as the improvement relation in the proof ("
        ++ show lawImpRel++")"
      let ctxKey = "ctx"
      assertInternal (Map.notMember ctxKey substitutions) $ "The substitution "
        ++"map (i.e. substitutions from the law) should not contain a "
        ++"substitution for "++ctxKey++", since it is used for the outer "
        ++"context."
      let lawLHSctx = Law.TAppCtx ctxKey lawLHS
          lawRHSctx = Law.TAppCtx ctxKey lawRHS
          substitutionsWctx = Map.insert ctxKey
                                         (T.SContext context)
                                         substitutions
          forbiddenNames = varFreeVars
      Log.logInfoN . pack $ "Checking side conditions."
      checkSideCondition sideCond substitutionsWctx varFreeVars
      Log.logInfoN . pack $ "Substituting into starting term (the "
        ++"left hand side in a left-to-right transformation)"
      substToLHS <- applySubstitution lawLHSctx
                                      sideCond
                                      substitutionsWctx
                                      forbiddenNames
                                      varFreeVars
      Log.logInfoN . pack $ "Checking that the substitutions into the starting "
        ++"law term is alpha-equal to the starting term."
      checkAlphaEqWrtLetReorder term1 substToLHS
      Log.logInfoN . pack $ "Substituting into law term of the transformed "
        ++"side (the right hand side in a left-to-right transformation)"
      substToRHS <- applySubstitution lawRHSctx
                                      sideCond
                                      substitutionsWctx
                                      forbiddenNames
                                      varFreeVars
      Log.logInfoN . pack $ "Checking that the substitutions into the "
        ++"transformed term is alpha-equal to the transformed term."
      checkAlphaEqWrtLetReorder substToRHS term2

-- | Given the law term L and two terms M and N,
-- this function checks alpha equivalance of M and N. If L contains let-terms
-- this function checks if M and N are equal with respect to alpha renaming and
-- reordering of let:s.
--
-- Currently, the implementation is very inefficient. It checks all
-- permutations of all let:s. Because of laziness, there are some computations
-- that are saved. Some things may also easily be paralellizable.
--
-- Subfunctions may be moved to base level
checkAlphaEqWrtLetReorder :: HasCallStack => T.Term -> T.Term -> CheckM ()
checkAlphaEqWrtLetReorder m n = do
  orderedEq <- isAlphaEquiv m n
  if orderedEq
    then return ()
    else
      let permutations = getAllLetPermutations m
      in if any (isOrderedAlphaEq n) permutations
              then return ()
              else throwCallstackError $ "Not alpha equivalent, even with "
                    ++ "reordering of let:s. Non-reordered difference: \n"
                    ++nonReorderedDiff
  where
    nonReorderedDiff = let (lnl1, _) = toLocallyNameless m
                           (lnl2, _) = toLocallyNameless n
                       in computeDifference lnl1 lnl2

    getAllLetPermutations :: T.Term -> [T.Term]
    getAllLetPermutations bigTerm = case bigTerm of
      T.TNonTerminating -> [bigTerm]
      T.TVar var -> [bigTerm]
      T.TNum i -> [bigTerm]
      T.TConstructor _ _ -> [bigTerm]
      T.TLam var term -> recursePerms term (T.TLam var)
      T.THole -> [bigTerm]
      T.TLet letBindings term ->
        let (vars, sws, hws, terms) = unzip4 letBindings
            a = map getAllLetPermutations terms :: [[T.Term]]
            -- a = permutations of let:s in inner terms
            b = combinations a :: [[T.Term]]
            -- b = combinations of permutations, which can make up a let
            c = map (zip4 vars sws hws) b :: [T.LetBindings]
            -- c = b, but turned into actual let:s with binding variable and
            -- weights
            d = map permutations c :: [[T.LetBindings]]
            -- d = all permutations of every combination of let bindings
            bindingPermutations = concat d :: [T.LetBindings]
            -- since every permutation is equally relevant, we concatinate.
            mainTermPermutations = getAllLetPermutations term :: [T.Term]
        in [T.TLet lbs term | lbs <- bindingPermutations
                              , term <- mainTermPermutations]

      T.TDummyBinds varSet term -> recursePerms term (T.TDummyBinds varSet)
      T.TStackSpikes sw term -> recursePerms term (T.TStackSpikes sw)
      T.THeapSpikes hw term -> recursePerms term (T.THeapSpikes hw)
      T.TRedWeight rw1 red -> case red of
        T.RApp term var ->
          recursePerms term (\t -> T.TRedWeight rw1 (T.RApp t var))
        T.RCase decideTerm cases ->
          let (constructors, boundVars, terms) = unzip3 cases
              termPerms = map getAllLetPermutations terms :: [[T.Term]]
              combinedTermPerms = combinations termPerms :: [[T.Term]]
              caseBranches = map (zip3 constructors boundVars) combinedTermPerms
                :: [[(String, [String], T.Term)]]
              decideTermPerms = getAllLetPermutations decideTerm :: [T.Term]
              allCaseTups = [(term, branches) | term <- decideTermPerms,
                                                branches <- caseBranches]
                :: [(T.Term, [(String, [String], T.Term)])]
           in map toCase allCaseTups
           where
            toCase (term, branches) = T.TRedWeight rw1 $ T.RCase term branches
        T.RPlusWeight term1 rw2 term2 ->
          let toPlus = \(t1, t2) -> T.TRedWeight rw1 (T.RPlusWeight t1 rw2 t2)
          in map toPlus $ combinedPermutations term1 term2
        T.RAddConst i term ->
          recursePerms term (\t -> T.TRedWeight rw1 (T.RAddConst i t))
        T.RIsZero term ->
          recursePerms term (\t -> T.TRedWeight rw1 (T.RIsZero t))
        T.RSeq term1 term2 ->
          map toSeq $ combinedPermutations term1 term2
          where
            toSeq (t1, t2) = T.TRedWeight rw1 $ T.RSeq t1 t2

    -- Given a list of lists, combines those permutations. For example,
    -- combinations ["ab","12", "xy"] = [ "a1x", "a1y", "a2x", "a2y"
    --                                  , "b1x", "b1y", "b2x", "b2y"]
    -- also works on lists of different lengths
    combinations :: [[a]] -> [[a]]
    combinations [] = [[]]
    combinations (p1:[]) = [[p] | p <- p1]
    combinations (p1:p2:[]) = [[a,b] | a <- p1, b <- p2]
    combinations (p1:ps) =
      let tailPerms = combinations ps
      in [h:t | h <- p1, t <- tailPerms]

    combinedPermutations :: T.Term -> T.Term -> [(T.Term, T.Term)]
    combinedPermutations term1 term2 =
      let perms1 = getAllLetPermutations term1
          perms2 = getAllLetPermutations term2
      in [(t1, t2) | t1 <- perms1, t2 <- perms2]

    recursePerms recurseTerm wrapTerm =
      let perms = getAllLetPermutations recurseTerm
      in map wrapTerm perms

    isOrderedAlphaEq :: T.Term -> T.Term -> Bool
    isOrderedAlphaEq m n = let (mLNL, _) = toLocallyNameless m
                               (nLNL, _) = toLocallyNameless n
                           in mLNL == nLNL

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module TermUtils (substituteFor
                 , isAlphaEquiv
                 , checkAlphaEquiv
                 , showSubstitute
                 , computeDifference) where

import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Except (MonadError)
import qualified Data.Set as Set
import Data.List.Extra (replace, intersperse)
import Data.Text (pack)

import qualified LocallyNameless as LNL
import qualified MiniTypedAST as T
import TermCorrectness (checkBoundVariablesDistinct, getFreeVariables
                       , getBoundVariables)
import OtherUtils (applyAndRebuild)
import CheckMonad (assert, CheckM)
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)
import ToPrettyLNL (showLNL)

-- | given M y and x, returns M[y/x]
substituteFor :: (HasCallStack, Log.MonadLogger m, MonadError String m) =>
                 T.Term -> String -> String -> m T.Term
substituteFor term y x = do
  checkBoundVariablesDistinct term
  assert (x `Set.member` getFreeVariables term)
    "you may only substitute a free variable."
  assert (y `Set.notMember` getBoundVariables term) $
    "Currently, the system only supports M[y/x] if y is not in the bound "
    ++"variables of M, for uniqueness of binding name reasons."
  return $ substitute y x term
  where
    substitute y x term = case term of
      T.TVar var | var == x -> T.TVar y
                 | otherwise -> T.TVar var
      T.TConstructor constrName vars ->
        let vars' = replace [x] [y] vars
        in T.TConstructor constrName vars'
      T.TDummyBinds varSet term ->
        let term' = substitute y x term
            varSet' = if Set.member x varSet
                        then Set.insert y $ Set.delete x varSet
                        else varSet
        in T.TDummyBinds varSet' term'
      T.TRedWeight rw (T.RApp term var) ->
        let term' = substitute y x term
            var' = if var == x then y else var
        in T.TRedWeight rw (T.RApp term' var')
      _ -> applyAndRebuild term (substitute y x)


class AlphaEq a where
  isAlphaEquiv :: HasCallStack => a -> a -> CheckM Bool
  checkAlphaEquiv :: HasCallStack => a -> a -> CheckM ()

instance AlphaEq T.Term where
  checkAlphaEquiv term1 term2 = do
    Log.logInfoN . pack $ "Checking that M and N are alpha equivalent"
    Log.logInfoN . pack $ "| where M = "++showTypedTerm term1
    Log.logInfoN . pack $ "| and   N = "++showTypedTerm term2
    Log.logInfoN . pack $ "| see debug output for details."
    alphaEq <- isAlphaEquiv term1 term2
    assert alphaEq $ "| The locally-nameless representation "
      ++"of M and N should be equal"

  isAlphaEquiv :: T.Term -> T.Term -> CheckM Bool
  isAlphaEquiv term1 term2 | term1 == term2 = return True
                           | otherwise = do
    Log.logDebugN . pack $ "Determining wheter M and N are alpha equivalent,"
    Log.logDebugN . pack $ "| where M = "++ showTypedTerm term1
    Log.logDebugN . pack $ "| and   N = "++showTypedTerm term2
    let (lnlTerm1, _) = toLocallyNameless term1
    let (lnlTerm2, _) = toLocallyNameless term2
    Log.logDebugN . pack $ "| Locally nameless representation of M is "
      ++showLNL lnlTerm1
    Log.logDebugN . pack $ "| Locally nameless representation of N is "
      ++ showLNL lnlTerm2
    return (lnlTerm1 == lnlTerm2)

showSubstitute :: T.Substitute -> String
showSubstitute = \case
  T.SLetBindings letBindings ->
    showTypedTerm letBindings
  T.SValue term -> showTypedTerm term
  T.SContext term -> showTypedTerm term
  T.SIntegerVar intExpr -> show intExpr
  T.SVar string -> string
  T.SVarVect strings -> show strings
  T.SValueContext term -> showTypedTerm term
  T.SReduction red -> showTypedTerm $ T.TRedWeight 1 red
  T.SVarSet stringSet ->
    let listForm = concat . intersperse ", " . Set.toList $ stringSet
    in "{" ++ listForm ++"}"
  T.STerm term -> showTypedTerm term
  T.STerms terms -> let strs = map showTypedTerm terms
                    in concat $ intersperse ", " strs
  T.SPatterns ptns -> show ptns
  T.SCaseStms stms -> let strStms = map showStm stms
                          everything = concat $ intersperse ", " strStms
                     in "{"++everything++"}"
    where
      showStm (constr, vars, term) =
        let vars' = concat $ intersperse " " vars
        in constr++" "++vars'++" -> "++showTypedTerm term
  T.SConstructorName str -> str

neq = "\n/=\n"

computeDifference :: LNL.Term -> LNL.Term -> String
computeDifference t1 t2 | t1 == t2 = "[error, no difference]"
computeDifference (LNL.TLam term1)
                  (LNL.TLam term2) = computeDifference term1 term2
computeDifference (LNL.TLet letBindings1 term1)
                  (LNL.TLet letBindings2 term2)
  | letBindings1 == letBindings2 = computeDifference term1 term2
  | term1 == term2 = lbDiff letBindings1 letBindings2
  | otherwise = showLNL (LNL.TLet letBindings1 term1)
                ++neq++showLNL (LNL.TLet letBindings2 term2)
  where
    lbDiff lbs1 lbs2 = let diff = takeWhile (\(a,b) -> a==b) $ zip lbs1 lbs2
                           (dlbs1, dlbs2) = unzip diff
                       in showLBs dlbs1++neq++showLBs dlbs2
    showLBs lbs = let mid = concat $ intersperse ", " $ map showLNL lbs
                  in "{" ++mid++ "}"
computeDifference (LNL.TDummyBinds varSet1 term1)
                  (LNL.TDummyBinds varSet2 term2)
  | varSet1 == varSet2 = computeDifference term1 term2
  | otherwise = showLNL (LNL.TDummyBinds varSet1 term1)
                ++neq++showLNL (LNL.TDummyBinds varSet2 term2)
computeDifference (LNL.TStackSpikes stackWeight1 term1)
                  (LNL.TStackSpikes stackWeight2 term2)
  | stackWeight1 == stackWeight2 = computeDifference term1 term2
  | otherwise = showLNL (LNL.TStackSpikes stackWeight1 term1)
                ++neq++ showLNL (LNL.TStackSpikes stackWeight2 term2)
computeDifference (LNL.THeapSpikes heapWeight1 term1)
                  (LNL.THeapSpikes heapWeight2 term2)
  | heapWeight1 == heapWeight2 = computeDifference term1 term2
  | otherwise = showLNL (LNL.THeapSpikes heapWeight1 term1)
                ++neq++showLNL (LNL.THeapSpikes heapWeight2 term2)
computeDifference (LNL.TRedWeight redWeight1 red1)
                  (LNL.TRedWeight redWeight2 red2)
  | redWeight1 == redWeight2 = case (red1, red2) of
    (LNL.RApp term1 var1 , LNL.RApp term2 var2)
      | var1 == var2 -> computeDifference term1 term2
    (LNL.RCase dTerm1 branches1, LNL.RCase dTerm2 branches2)
      | branches1 == branches2 -> computeDifference dTerm1 dTerm2
    (LNL.RPlusWeight term11 rw1 term12, LNL.RPlusWeight term21 rw2 term22)
      | term11 == term21 && rw1 == rw2 -> computeDifference term12 term22
      | rw1 == rw2 && term12 ==  term22 -> computeDifference term11 term21
    (LNL.RAddConst int1 term1, LNL.RAddConst int2 term2)
      | int1 == int2 -> computeDifference term1 term2
    (LNL.RIsZero term1, LNL.RIsZero term2) -> computeDifference term1 term2
    (LNL.RSeq term11 term12, LNL.RSeq term21 term22)
      | term11 == term21 -> computeDifference term12 term22
      | term12 == term22 -> computeDifference term11 term21
    (_,_) -> showLNL red1 ++neq++showLNL red2
  | otherwise = showLNL (LNL.TRedWeight redWeight1 red1)
                ++neq++showLNL (LNL.TRedWeight redWeight2 red2)
computeDifference t1 t2 = showLNL t1++neq++showLNL t2

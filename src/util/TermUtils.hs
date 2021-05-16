{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module TermUtils (substituteFor
                 , isAlphaEquiv
                 , checkAlphaEquiv
                 , showSubstitute) where

import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Except (MonadError)
import qualified Data.Set as Set
import Data.List.Extra (replace, intersperse)
import Data.Text (pack)

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

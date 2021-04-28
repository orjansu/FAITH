module Matcher (addProofDetails) where

import Data.Map.Lazy as Map
import Data.List (unzip4, zip4)

import TypedLawAST as Law
import qualified MiniTypedAST as T
import CheckMonad (CheckM)
import TermCorrectness (isValue)

-- | Given a proof script with some details left out, and sends a list of
-- possible proofs with the details filled in, or throws an error in the CheckM
-- monad. Currently, these details are the substitutions that are not specified
-- by the user.
addProofDetails :: T.ProofScript -> Either [String] [T.ProofScript]
addProofDetails = undefined

match :: Law.Term -> T.Term -> T.Substitutions -> Maybe [T.Substitutions]
match (Law.TValueMetaVar mvName) term subst = if isValue term
  then Just [Map.singleton mvName (T.SValue term)]
  else Nothing
match (Law.TVar mvName) (T.TVar var) subst =
  Just [Map.singleton mvName (T.SVar var)]
match (Law.TAppCtx mvName lawTerm) term subst = undefined
match (Law.TLet lawBinds lawTerm) (T.TLet termBinds term) subst = do
  mainMatches <- match lawTerm term subst
  let (lVars, lsws, lhws, lbinds) = unzip4 lawBinds
  undefined
match (Law.TDummyBinds varSet lawTerm) term subst = undefined
match _ _ _ = Nothing

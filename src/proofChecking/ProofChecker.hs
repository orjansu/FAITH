{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module ProofChecker where

import qualified Control.Monad.Logger as Log
import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Data.Text (pack, Text)
import Data.Maybe
import qualified Data.Set as Set

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import qualified LanguageLogic as Lang
import qualified Common as Com (ImpRel(..))
import ToLocallyNameless (toLocallyNameless)
import qualified LocallyNameless as LNL
import ToPrettyLNL (showLNL)
import ShowTypedTerm (showTypedTerm)

newtype CheckM a = MkM {getM :: (ExceptT String
                                  (Log.WriterLoggingT Identity) a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String)

instance MonadFail CheckM where
  fail str = throwError str

-- | Checks whether a detailed proof script is correct. Returns a [String],
-- containing a log and error message if it is incorrect, and Nothing
-- if it is correct.
--
-- Assumes that the incoming proof script is typechecked.
checkDetailedProof :: T.ProofScript -> Maybe [String]
checkDetailedProof proofScript = runCheckM $ check proofScript

runCheckM :: CheckM () -> Maybe [String]
runCheckM monadComputation =
  let r = runIdentity $
            Log.runWriterLoggingT $
                runExceptT $
                  getM $
                    monadComputation
  in case r of
    (Right (), logs) -> Nothing
    (Left errorMsg, logs) -> Just $(map toLine logs) ++ [errorMsg]

toLine :: Log.LogLine -> String
toLine (loc, logsource, loglevel, logstr) =
  (show logstr)

class Checkable a where
  check :: a -> CheckM ()

instance Checkable T.ProofScript where
  check (T.DProofScript theorems) = mapM check theorems >> return ()

instance Checkable T.Theorem where
  check (T.DTheorem (T.DProposition freeVars start imprel goal) proof) = do
    checkProofSteps proof start imprel freeVars goal

type GlobalImpRel = Com.ImpRel
type Start = T.Term
type Goal = T.Term

checkProofSteps :: T.Proof
                   -> Start
                   -> GlobalImpRel
                   -> T.FreeVars
                   -> Goal
                   -> CheckM ()
checkProofSteps (T.Simple proofSteps) start globalImpRel freeVars goal = do
  let (T.PSMiddle startTerm _ _ _ _) = head proofSteps
  checkAlphaEquiv start startTerm
  mapM (checkStep globalImpRel freeVars) proofSteps
  let (T.PSMiddle _ _ _ _ endTerm) = last proofSteps
  checkAlphaEquiv goal endTerm

-- | Checks if a single step is valid. This computation may be run
-- independently in parallel for each step to speed things up if that is an
-- issue. Could maybe use the globally free variables to speed things up later.
checkStep :: GlobalImpRel -> T.FreeVars -> T.ProofStep -> CheckM ()
checkStep globalImpRel
          freeVars
          (T.PSMiddle term1 subterm command localImpRel term2) = do
  Log.logInfoN . pack $ "checking that "++showTypedTerm term1++" "
  Log.logInfoN . pack $ show localImpRel
  Log.logInfoN . pack $ showTypedTerm term2
  Log.logInfoN . pack $ "by transforming "++showTypedTerm subterm
  Log.logInfoN . pack $ "using the law "++show command
  Log.logInfoN . pack $ "with the global improvement relation being "
    ++show globalImpRel
  assert (localImpRel `Lang.impRelImplies` globalImpRel)
    $ show localImpRel ++ " should imply "++ show globalImpRel
  case command of
    T.AlphaEquiv -> checkAlphaEquiv term1 term2
    T.Law (Law.DLaw lawName lawLHS lawImpRel lawRHS)
          substitutions -> do
      assert (lawImpRel == localImpRel) "The improvement relation of the law must be the same as the improvement relation in the proof"
      context <- getContext subterm term1
      let contextVars = getAllVars context
      Log.logInfoN . pack $ "applying substitution from subterm to law"
      -- TODO log messages
      substToLHS <- applySubstitution lawLHS substitutions contextVars
      checkAlphaEquiv subterm substToLHS
      substToRHS <- applySubstitution lawLHS substitutions contextVars
      fvOrig <- getFreeVars subterm
      fvTransformed <- getFreeVars substToRHS
      assert (fvOrig == fvTransformed) "The transformation should not make bound variables free."
      rhsTerm <- applyContext context substToRHS

      -- This shows that we could generate the next term ourselves instead.
      -- However, it is more important to typecheck rhsTerm if we generate it.
      checkAlphaEquiv rhsTerm term2

      -- This check below should not be needed. Quickcheck it later and maybe
      -- remove if it impedes performance.
      Log.logInfoN . pack $ "Checking that the resulting term of the transformation typechecks."
      typeCheck rhsTerm freeVars
      return undefined

-- | Given the subtermterm M and the whole term N, this function returns the
-- context C such that C[M] = N. This equivalence is strict equivalence and not
-- alpha equivalence.
--
-- Fails if M is not a subterm of N
-- TODO think about the case if there are more than one hole
-- TODO This failed because you might get to the case where the subterm is
-- present in more than one place in the term. Instead, you will need to
-- specify the context instead, and use this getContext in the typechecker.
getContext :: T.Term -> T.Term -> CheckM T.Term
getContext term1 term2 = do
  Log.logInfoN $ pack $ "Checking if M is a subterm of N, i.e. if there is a "
    ++"C such that C[M] = N"
  Log.logInfoN $ pack $ "| where M = "++showTypedTerm term1
  Log.logInfoN $ pack $ "| and N = "++showTypedTerm term2
  case getContext' term1 term2 of
    Just context -> return context
    Nothing -> fail notSubTerm
  where
    -- | given M and N, returns C such that C[M] = N
    getContext' :: T.Term -> T.Term -> Maybe T.Term
    getContext' subterm term | subterm == term = return T.THole
    getContext' subterm (T.TVar _) = Nothing
    getContext' subterm (T.TNum _) = Nothing
    getContext' subterm (T.TLam var term)
      | subterm == term = return (T.TLam var T.THole)
      | isJust subMatch = let Just ctx = subMatch
                          in return $ T.TLam var ctx
      where subMatch = getContext' subterm term
    getContext' subterm T.THole = Nothing --This should not happen.
    getContext' subterm (T.TLet letBindings term)
      | subterm == term = return (T.TLet letBindings T.THole)
      where
        matchLetBindings subterm [] = Nothing

        matchLetBinding (var, sw, hw, term) | subterm == term = T.THole

    notSubTerm :: String
    notSubTerm = "| M is not a subterm of N."


-- | Given C and M, where C is a context and M is a term, returns C[M].
-- TODO Currently only supports contexts with a single hole
applyContext :: T.Term -> T.Term -> CheckM T.Term
applyContext = undefined

-- | Given a term, returns the set of all variable names used in that term,
-- regardless of if the variables are free or bound
getAllVars :: T.Term -> Set.Set String
getAllVars (T.TVar var) = Set.singleton var
getAllVars (T.TNum integer) = Set.empty
getAllVars (T.TLam var term) = Set.singleton var `Set.union` getAllVars term
getAllVars (T.THole) = Set.empty
getAllVars (T.TLet letBindings term) =
  getLBSVars letBindings `Set.union` getAllVars term
  where
    getLBSVars = Set.unions . map getLBVars
    getLBVars :: (String, T.StackWeight, T.HeapWeight, T.Term) -> Set.Set String
    getLBVars (name, _sw, _hw, term) = let termSet = getAllVars term
                                       in Set.insert name termSet
getAllVars (T.TDummyBinds varSet term) = varSet `Set.union` getAllVars term
getAllVars (T.TRedWeight _redWeight red) =
  case red of
    T.RApp term var -> let termSet = getAllVars term
                       in Set.insert var termSet
    T.RPlusWeight term1 _rw term2 ->
      getAllVars term1 `Set.union` getAllVars term2

-- | Given M, sigma and S, where M is a law term with meta-
-- variables, sigma is a substitution that substitutes all meta-
-- variables for concrete variables and S is a set of variable names,
-- this function returns sigma applied to M, such that the names of the bound
-- variables in the result are unique, both with respect to the result term
-- and the variable names in S.
--
-- Fails if sigma doesn't contain substitutions for all meta-variables in M.
applySubstitution :: Law.Term
                  -> T.Substitutions
                  -> Set.Set String
                  -> CheckM T.Term
applySubstitution = undefined

-- | Finds the names of the free variables of the term
getFreeVars :: T.Term -> CheckM (Set.Set String)
getFreeVars term = do
  (_lnlTerm, freeVars) <- runToLocallyNameless term
  return freeVars

-- | Checks whether the term type-checks, i.e. if all variables are bound or
-- declared free.
--
-- Status: one way is tp unpype it and run it through the normal typechecker.
-- It is ineffective, but it relies on the single implementation of
-- typechecking. A better approach might be to divide the typechecker into one
-- phase that converts and one that typechecks. TODO typechecker needs more
-- context to be able to typecheck a term instead of the whole program
typeCheck :: T.Term -> T.FreeVars -> CheckM ()
typeCheck = undefined

checkAlphaEquiv :: T.Term -> T.Term -> CheckM ()
checkAlphaEquiv term1 term2 = do
  Log.logInfoN . pack $ "Checking that M and N are alpha equivalent"
  Log.logInfoN . pack $ "| where M = "++showTypedTerm term1
  Log.logInfoN . pack $ "| and N = "++showTypedTerm term2
  Log.logInfoN . pack $ "| see debug output for details."
  alphaEq <- isAlphaEquiv term1 term2
  assert alphaEq $ "| The locally-nameless representation "
    ++"of M and N should be equal"

isAlphaEquiv :: T.Term -> T.Term -> CheckM Bool
isAlphaEquiv term1 term2 | term1 == term2 = return True
                         | term1 /= term2 = do
  Log.logDebugN . pack $ "Determining wheter M and N are alpha equivalent,"
  Log.logDebugN . pack $ "| where M = "++ showTypedTerm term1
  Log.logDebugN . pack $ "| and N = "++showTypedTerm term2
  (lnlTerm1, _) <- runToLocallyNameless term1
  (lnlTerm2, _) <- runToLocallyNameless term2
  Log.logDebugN . pack $ "| Locally nameless representation of M is  "
    ++showLNL lnlTerm1
  Log.logDebugN . pack $ "| Locally nameless representation of N is "
    ++ showLNL lnlTerm2
  return (lnlTerm1 == lnlTerm2)

runToLocallyNameless :: T.Term -> CheckM (LNL.Term, Set.Set String)
runToLocallyNameless = liftEither . toLocallyNameless

liftEither :: Either String a -> CheckM a
liftEither (Left errorMsg) = throwError errorMsg
liftEither (Right a) = return a

assert :: Bool -> String -> CheckM ()
assert True _ = return ()
assert False description = throwError $ "assertion failed: "++description

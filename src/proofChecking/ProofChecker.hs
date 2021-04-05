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
import Data.Text (pack)
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
-- context C such that C[M] = N
--
-- Fails if M is not a subterm of N
getContext :: T.Term -> T.Term -> CheckM T.Term
getContext = undefined

-- | Given C and M, where C is a context and M is a term, returns C[M].
-- TODO Currently only supports contexts with a single hole
applyContext :: T.Term -> T.Term -> CheckM T.Term
applyContext = undefined

-- | Given a term, returns the set of all variable names used in that term,
-- regardless of if the variables are free or bound
getAllVars :: T.Term -> Set.Set String
getAllVars = undefined

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
getFreeVars = undefined

-- | Checks whether the term type-checks, i.e. if all variables are bound or
-- declared free.
typeCheck :: T.Term -> T.FreeVars -> CheckM ()
typeCheck = undefined

checkAlphaEquiv :: T.Term -> T.Term -> CheckM ()
checkAlphaEquiv term1 term2 = do
  (lnlTerm1, _) <- runToLocallyNameless term1
  (lnlTerm2, _) <- runToLocallyNameless term2
  Log.logInfoN . pack $ "Locally nameless representation of first term is  "
    ++showLNL lnlTerm1
  Log.logInfoN . pack $ "Locally nameless representation of second term "
    ++"is " ++ showLNL lnlTerm2
  assert (lnlTerm1 == lnlTerm2) $ "The locally-nameless representation of "
    ++"the terms should be equal."

runToLocallyNameless :: T.Term -> CheckM (LNL.Term, Set.Set String)
runToLocallyNameless = liftEither . toLocallyNameless

liftEither :: Either String a -> CheckM a
liftEither (Left errorMsg) = throwError errorMsg
liftEither (Right a) = return a

assert :: Bool -> String -> CheckM ()
assert True _ = return ()
assert False description = throwError $ "assertion failed: "++description

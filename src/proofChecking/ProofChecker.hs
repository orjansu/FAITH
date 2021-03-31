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
  check (T.DTheorem proposition proof) = do
    let (_termVars, _freeVars, start, imprel, goal) = getInfo proposition
    checkProofSteps proof start imprel goal
    where
      getInfo (T.DProposition (T.DFreeVars termVars vars) start imprel goal) =
        (termVars, vars, start, imprel, goal)

type GlobalImpRel = T.ImpRel
type Start = T.Term
type Goal = T.Term

checkProofSteps :: T.Proof -> Start -> GlobalImpRel -> Goal -> CheckM ()
checkProofSteps (T.Simple proofSteps) start globalImpRel goal = do
  let (T.PSMiddle startTerm _ _ _ _) = head proofSteps
  checkAlphaEquiv start startTerm
  mapM (checkStep globalImpRel) proofSteps
  let (T.PSMiddle _ _ _ _ endTerm) = last proofSteps
  checkAlphaEquiv goal endTerm

-- | Checks if a single step is valid. This computation may be run
-- independently in parallel for each step to speed things up if that is an
-- issue. Could maybe use the globally free variables to speed things up later.
checkStep :: GlobalImpRel -> T.ProofStep -> CheckM ()
checkStep globalImpRel (T.PSMiddle term1 subterm command localImpRel term2) = do
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
    Law.AlphaEquiv -> checkAlphaEquiv term1 term2

checkAlphaEquiv :: T.Term -> T.Term -> CheckM ()
checkAlphaEquiv term1 term2 = do
  (lnlTerm1, _) <- runToLocallyNameless term1
  (lnlTerm2, _) <- runToLocallyNameless term2
  Log.logInfoN . pack $ "Locally nameless representation of first term is "
    ++showLNL lnlTerm1
  Log.logInfoN . pack $ "Locally nameless representation of second term "
    ++"is" ++ showLNL lnlTerm2
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

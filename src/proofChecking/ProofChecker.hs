{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}


module ProofChecker where

import qualified Control.Monad.Logger as Log
import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.State (StateT, MonadState, runStateT, gets, modify)
import Control.Monad.Trans.Maybe
import Data.Text (pack)
import Data.Maybe
import qualified Data.Set as Set

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law

data CheckSt = MkSt { start :: T.Term
                    , globalImpRel :: T.ImpRel
                    , goal :: T.Term
                    , freeTermVars :: Set.Set String
                    , freeVars :: Set.Set String
                    }

initSt = MkSt {}

newtype CheckM a = MkM {getM :: (MaybeT
                                 (StateT CheckSt
                                  (Log.WriterLoggingT Identity)) a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadFail,
            MonadState CheckSt)

throwError :: String -> CheckM ()
throwError str = do
  Log.logErrorN $ pack str
  fail ""

-- | Checks whether a detailed proof script is correct. Returns a [String],
-- containing a log and error message if it is incorrect, and Nothing
-- if it is correct.
--
-- Assumes that the incoming proof script is typechecked.
checkDetailedProof :: T.ProofScript -> Maybe [String]
checkDetailedProof proofScript =
  let r = runIdentity $
            Log.runWriterLoggingT $
              (flip runStateT) initSt $
                runMaybeT $
                  getM $
                    check proofScript
  in case r of
    ((Just (), st), logs) -> Nothing
    ((Nothing, st), logs) -> Just $ map toLine logs

toLine :: Log.LogLine -> String
toLine (loc, logsource, loglevel, logstr) = 
  (show logsource)++":2"++(show loglevel)++":3"++(show logstr)

class Checkable a where
  check :: a -> CheckM ()

instance Checkable T.ProofScript where
  check (T.DProofScript theorems) = mapM check theorems >> return ()

instance Checkable T.Theorem where
  check (T.DTheorem proposition proof) = do
    check proposition
    check proof

instance Checkable T.Proposition where
  check (T.DProposition (T.DFreeVars termVars vars) start imprel goal) = do
    modify (\st -> st{ start = start
                     , globalImpRel = imprel
                     , goal = goal
                     , freeTermVars = termVars
                     , freeVars = vars
                      })

instance Checkable T.Proof where
  check (T.Simple proofsteps) = undefined

type GlobalImpRel = T.ImpRel
checkStep :: T.ProofStep -> GlobalImpRel -> Bool -- TODO
checkStep = undefined

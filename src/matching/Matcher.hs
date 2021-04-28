module Matcher (addProofDetails) where

import qualified MiniTypedAST as T
import CheckMonad (CheckM)

-- | Given a proof script with some details left out, and sends a list of
-- possible proofs with the details filled in, or throws an error in the CheckM
-- monad. Currently, these details are the substitutions that are not specified
-- by the user.
addProofDetails :: T.ProofScript -> Either [String] [T.ProofScript]
addProofDetails = undefined

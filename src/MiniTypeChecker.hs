{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MiniTypeChecker where

import qualified AbsSie as UT
import qualified MiniTypedAST as T

import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity


data MySt = MkSt { bindingVarNames :: Set.Set String
                 , contexts :: [Set.Set String]
                 }

initSt :: MySt
initSt = let bindingVarNames = Set.empty
             contexts = []
         in MkSt {bindingVarNames = bindingVarNames, contexts = contexts}

newtype CheckM a = Mk {getM :: (StateT MySt (ExceptT String Identity) a)}
  deriving (Functor, Applicative, Monad, MonadState MySt, MonadError String)

instance MonadFail CheckM where
    fail str = throwError str

typecheck :: UT.ProofScript -> Either String T.ProofScript
typecheck untypedProofScript = do
  let res = runIdentity (
              runExceptT (
                runStateT
                  (getM (checkScript untypedProofScript))
                  initSt
                )
              )
  case res of
    Left errorMsg                    -> Left errorMsg
    Right (typedProofScript, _state) -> Right typedProofScript

checkScript :: UT.ProofScript -> CheckM T.ProofScript
checkScript (UT.DProofScript (UT.DProgBindings []) [t]) = do
  tTheorem <- checkTheorem t
  return $ T.DProofScript [] [tTheorem]
checkScript _ = fail "not implemented yet"

checkTheorem :: UT.Theorem -> CheckM T.Theorem
checkTheorem (UT.DTheorem (UT.DProposition UT.NoContext
                          (UT.WithForall [(UT.SmallVar y)])
                                     start
                                     UT.StrongImprovementLR
                                     goal) proof) = do
  tStart <- checkTerm start
  tGoal <- checkTerm goal
  tProof <- checkProof proof
  -- let freeVars = DFreeVars (Set.fromList [])
  --let prop = T.DProposition False
  return undefined
checkTheorem _ = fail "not implemented yet"

checkTerm = undefined

checkProof = undefined

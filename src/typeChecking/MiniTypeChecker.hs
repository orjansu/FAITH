{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

module MiniTypeChecker where

import qualified AbsSie as UT
import qualified MiniTypedAST as T
import qualified TypedLawAST as Law

import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity


data MySt = MkSt {letContext :: Maybe T.LetBindings}

initSt :: MySt
initSt = MkSt {letContext = error "should have been initialized before use"}

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

--- Utility
-- converts the term M to let G in M if G is the context of the proof.
-- That is, if the proposition is:
-- proposition: G |- M <~> N
-- and a term M1 is passed to this function, the function returns
-- let G in M1
-- but if the proposition is:
-- proposition |- M <~> N
-- then this function is the identity function.
-- Cannot be used before the context is parsed.
withLetContext :: T.Term -> CheckM T.Term
withLetContext startTerm = do
  context <- gets letContext
  case context of
    Nothing -> return startTerm
    Just letBindings -> return $ T.TLet letBindings startTerm

-- Main

checkScript :: UT.ProofScript -> CheckM T.ProofScript
checkScript (UT.DProofScript (UT.DProgBindings []) [t]) = do
  tTheorem <- checkTheorem t
  return $ T.DProofScript [] [tTheorem]
checkScript _ = fail "not implemented yet 1"

checkTheorem :: UT.Theorem -> CheckM T.Theorem
checkTheorem (UT.DTheorem (UT.DProposition UT.NoContext
                                     freeVars
                                     start
                                     UT.WeakCostEquiv
                                     goal) proof) = do
  modify (\st -> st{letContext = Nothing})
  addFreeVars freeVars
  tStart <- check start
  tGoal <- check goal
  tProof <- check proof
  -- let prop = T.DProposition False
  return undefined
checkTheorem _ = fail "not implemented yet 2"

class Checkable a where
  type TypedVersion a
  check :: a -> CheckM (TypedVersion a)

instance Checkable UT.Term where
  type TypedVersion UT.Term = T.Term
  -- | Checks a term, which consists of the following:
  -- - Converts to T.Term.
  -- - Checks that all variable names are unique wrt the whole term (TODO)
  -- - Does not: Checks typing of a typical lambda calculus
  -- - Variables are declared or bound (TODO)
  -- - General terms, i.e. any(M) are declare free (TODO)
  -- - Stack weight expressions: See checkWeightExpr
  check :: UT.Term -> CheckM T.Term
  check (UT.TAny)                          = fail "not implemented yet 3"
  check (UT.TTermVar capitalIdent)         = fail "not implemented yet 4"
  check (UT.TNonTerminating)               = fail "not implemented yet 5"
  check (UT.TVar var)                      = do
    tVar <- checkMentionedVar var
    return $ T.TVar tVar
  check (UT.TIndVar var indExpr)           = fail "not implemented yet 6"
  check (UT.TNum integer)                  = return $ T.TNum integer
  check (UT.THole)                         = return T.THole
  check (UT.TConstructor constructor)      = fail "not implemented yet 7"
  check (UT.TLam var term)                 = do
    tVar <- checkBindingVarUnique var
    -- TODO add the var to the binding list for lambdas
    tTerm <- check term
    return $ T.TLam tVar tTerm
  check (UT.TLet letBindings term)         = do
    tLetBindings <- check letBindings
    tTerm <- check term
    return $ T.TLet tLetBindings tTerm
  check (UT.TStackSpike term)              = fail "not implemented yet 8"
  check (UT.TStackSpikes stackWeight term) = fail "not implemented yet 9"
  check (UT.THeapSpike term)               = fail "not implemented yet 10"
  check (UT.THeapSpikes heapWeight term)   = fail "not implemented yet 11"
  check (UT.TDummyBinds varSet term)       = do
    tVarSet <- check varSet
    tTerm <- check term
    return $ T.TDummyBinds tVarSet tTerm
  check (UT.TRedWeight redWeight red)      = do
    case redWeight of
      UT.DRedWeight (UT.StackWeightExpr (UT.IENum n)) -> do
        tRed <- check red
        return $ T.TRedWeight n tRed
      _ -> fail "not implemented yet"
  check (UT.TRed red)                      = do
    tRed <- check red
    return $ T.TRedWeight 1 tRed

instance Checkable UT.LetBindings where
  type TypedVersion UT.LetBindings = T.LetBindings
  check UT.LBSAny = fail "not implemented yet 12"
  check (UT.LBSVar capitalIdent) = fail "not implemented yet"
  check (UT.LBSSet bindingSetList) = do
    tLetBindings <- mapM checkSingle bindingSetList
    return tLetBindings
    where
      checkSingle :: UT.LetBinding
                     -> CheckM (T.Name, T.StackWeight, T.HeapWeight, T.Term)
      checkSingle UT.LBAny = fail "not implemented yet 13"
      checkSingle (UT.LBConcrete var UT.BSNoWeight term) = do
        tVar <- checkBindingVarUnique var
        -- TODO add var to let binding list
        tTerm <- check term
        return (tVar, 1,1, tTerm)
      checkSingle (UT.LBConcrete var withWeight term) =
        fail "not implemented yet 14"


instance Checkable UT.VarSet where
  type TypedVersion UT.VarSet = T.VarSet
  check (UT.DVarSet vars) = do
    tVars <- mapM checkMentionedVar vars
    return $ Set.fromList tVars

instance Checkable UT.Red where
  type TypedVersion UT.Red = T.Red
  check (UT.RCase term caseStms)               = fail "not implemented yet 15"
  check (UT.RApp term var)                     = do
    tTerm <- check term
    tVar <- checkMentionedVar var
    return $ T.RApp tTerm tVar
  check (UT.RAddConst integer term)            = fail "not implemented yet 16"
  check (UT.RIsZero term)                      = fail "not implemented yet 17"
  check (UT.RSeq term1 term2)                  = fail "not implemented yet 18"
  check (UT.RPlusWeight term1 redWeight term2) = fail "not implemented yet 19"
  check (UT.RPlus term1 term2)                 = do
    tTerm1 <- check term1
    tTerm2 <- check term2
    return $ T.RPlusWeight tTerm1 1 tTerm2

-- | TODO check that the var is bound or declared free
checkMentionedVar :: UT.Var -> CheckM T.Var
checkMentionedVar (UT.DVar (UT.Ident name)) = return name

-- | TODO:
-- - Check that the binding var is not declared before
-- (in that case rename or return something else?)
checkBindingVarUnique :: UT.Var -> CheckM T.Var
checkBindingVarUnique (UT.DVar (UT.Ident name)) = return name

instance Checkable UT.Proof where
  type TypedVersion UT.Proof = T.Proof
  check (UT.PByFPInduction indVar baseCase indCase UT.DQed) =
    fail "not implemented yet"
  check (UT.PStraightForward steps UT.DQed) = do
    tSteps <- checkSteps1 steps
    return $ T.Simple tSteps
    where
      -- | Note: The steps after the HereMarker ($) are not processed.
      -- TODO: if first term is not specified, sunstitute for the goal. note
      -- that this doesn't work in the inductive case.
      checkSteps1 :: [UT.ProofStep] -> CheckM T.SubProof
      checkSteps1 [] = return []
      checkSteps1 (UT.PSHereMarker:cmds) = return []
      checkSteps1 ((UT.PSFirstTerm term1)
                     :(UT.PSCmd subterm transCmd)
                     :(UT.PSTerm imprel term2)
                     :cmds) = do
        proofStep <- checkProofStep term1 subterm transCmd imprel
        proofSteps <- checkSteps2 $ (UT.PSTerm imprel term2):cmds
        return $ proofStep:proofSteps
      checkSteps1 _ = fail $ "Terms and commands in first two steps "
                             ++"are not specified or wrongly formatted"

      -- TODO: What happens when HereMarker is in the second or third term?
      checkSteps2 :: [UT.ProofStep] -> CheckM T.SubProof
      checkSteps2 [] = return []
      checkSteps2 (UT.PSHereMarker:cmds) = return []
      checkSteps2 (_:UT.PSHereMarker:cmds) = fail $ "placement of here-marker "
        ++ "$ not supported yet. Please move it one step up or down."
      checkSteps2 ((UT.PSTerm _imprel1 term1)
                   :(UT.PSCmd subterm transCmd)
                   :(UT.PSTerm imprel2 term2)
                   :cmds) = do
        proofStep <- checkProofStep term1 subterm transCmd imprel2
        proofSteps <- checkSteps2 $ (UT.PSTerm imprel2 term2):cmds
        return $ proofStep:proofSteps
      checkSteps2 ((UT.PSTerm _imprel term)
                   :(UT.PSQed UT.DQed)
                   :[]) = do
        tTerm <- check term
        return $ [T.PSEnd tTerm]
      checkSteps2 _ = fail $ "Ordering of proof steps are invalid. Every other "
                           ++"step must be a term and every other a "
                           ++"transformational command."

      checkProofStep :: UT.Term -> UT.SubTerm -> UT.TransCmd -> UT.ImpRel
                        -> CheckM T.ProofStep
      checkProofStep term1 subterm transCmd imprel = do
        tTerm1 <- check term1
        tTerm1withCtx <- withLetContext tTerm1
        command <- check transCmd
        tSubTerm <- getSubTerm subterm tTerm1
        tImprel <- check imprel
        let proofStep = T.PSMiddle tTerm1withCtx tSubTerm command tImprel
        return proofStep
  check (UT.PGeneral commandName cmdArgs subProofs UT.DQed) =
    fail "not implemented yet 20"

-- | Takes an expression (or command) for a subterm and the term it expresses
-- a subterm of, and returns the corresponding typed subterm if exactly one
-- such subterm exists. Throws an error otherwise.
-- Parameters: subterm-expression, term (without let-context)
-- returns: the term expressed by the subterm-expression.
getSubTerm :: UT.SubTerm -> T.Term -> CheckM T.Term
getSubTerm UT.STWholeWithCtx term = withLetContext term
getSubTerm UT.STShown term = return term
getSubTerm (UT.STTerm subtermExpr) term = fail "not implemented yet 21"
getSubTerm UT.STGuess term = fail "not implemented yet 22"

instance Checkable UT.ImpRel where
  type TypedVersion UT.ImpRel = T.ImpRel
  check UT.DefinedEqual        = return T.DefinedEqual
  check UT.StrongImprovementLR = return T.StrongImprovementLR
  check UT.WeakImprovementLR   = fail "not implemented yet 23"
  check UT.StrongImprovementRL = fail "not implemented yet 24"
  check UT.WeakImprovementRL   = fail "not implemented yet 25"
  check UT.StrongCostEquiv     = fail "not implemented yet 26"
  check UT.WeakCostEquiv       = fail "not implemented yet 27"

instance Checkable UT.TransCmd where
  type TypedVersion UT.TransCmd = Law.Command
  check (UT.CmdSpecial UT.STCAlphaEquiv) = return Law.AlphaEquiv
  check (UT.CmdSpecial (UT.STCReorderLet varOrder)) =
    fail "not implemented yet 28"
  check (UT.CmdSpecial (UT.STCReorderCase varOrder)) =
    fail "not implemented yet 29"
  check (UT.CmdGeneral cmdName args)  = fail "not implemented yet 30"

-- | TODO add the free variables to the context
addFreeVars :: UT.Free -> CheckM ()
addFreeVars _ = return ()

-- | Checks if a weight expression is correct.
-- - if it contains variables, the variables must be declared to be free
checkWeightExpr = undefined

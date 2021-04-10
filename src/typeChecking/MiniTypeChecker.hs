{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

module MiniTypeChecker where

import qualified AbsSie as UT
import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import qualified Common as Com (ImpRel(..))

import qualified Data.Set as Set
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.State (StateT, runStateT, gets, MonadState, modify)
import Data.Functor.Identity (Identity, runIdentity)

data MySt = MkSt {letContext :: Maybe T.LetBindings
                 , start :: T.Term
                 , goal :: T.Term
                 }

initSt :: MySt
initSt = MkSt {letContext = undefined, start= undefined, goal = undefined}

newtype CheckM a = Mk {getM :: (StateT MySt (ExceptT String Identity) a)}
  deriving (Functor, Applicative, Monad, MonadState MySt, MonadError String)

instance MonadFail CheckM where
    fail str = throwError str

typecheck :: UT.ProofScript -> Either String T.ProofScript
typecheck untypedProofScript = do
  let res = runIdentity (
              runExceptT (
                runStateT
                  (getM (check untypedProofScript))
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

-- | the inverse of withLetContext
removeImplicitLet :: T.Term -> CheckM T.Term
removeImplicitLet startTerm = do
  context <- gets letContext
  case context of
    Nothing -> return startTerm
    Just _ -> case startTerm of
      T.TLet _ inner -> return inner
      _ -> fail "internal: Tried to remove implicit let but there is none."

class Checkable a where
  type TypedVersion a
  check :: a -> CheckM (TypedVersion a)

instance Checkable UT.ProofScript where
  type TypedVersion UT.ProofScript = T.ProofScript
  check (UT.DProofScript (UT.DProgBindings []) [t]) = do
    tTheorem <- check t
    return $ T.DProofScript [tTheorem]
  check _ = fail "not implemented yet 1"

instance Checkable UT.Theorem where
  type TypedVersion UT.Theorem = T.Theorem
  check (UT.DTheorem (UT.DProposition UT.NoContext
                                       freeVars
                                       start
                                       UT.DefinedEqual
                                       goal) proof) = do
    modify (\st -> st{letContext = Nothing})
    tFreeVars <- check freeVars
    -- TODO add freeVars to ctx
    tStart <- check start
    tGoal <- check goal
    modify (\st -> st{start = tStart, goal = tGoal})
    tProof <- check proof
    let prop = T.DProposition tFreeVars tStart Com.DefinedEqual tGoal
    return $ T.DTheorem prop tProof
  check _ = fail "not implemented yet 2"


instance Checkable UT.Free where
  type TypedVersion UT.Free = T.FreeVars
  check (UT.WithFree freeVars) =
    let
      termVarList = filter isTermVar freeVars
      termVarStrings = map getString termVarList
      termVarSet = Set.fromList termVarStrings
      varList = filter (not . isTermVar) freeVars
      varListStrings = map getString varList
      varSet = Set.fromList varListStrings
    in return $ T.DFreeVars termVarSet varSet
    where
      isTermVar :: UT.VarAnyType -> Bool
      isTermVar (UT.BigVar _) = True
      isTermVar (UT.SmallVar _) = False
      getString :: UT.VarAnyType -> String
      getString (UT.BigVar (UT.CapitalIdent name)) = name
      getString (UT.SmallVar (UT.Ident name)) = name
  check UT.NoFree = return $ T.DFreeVars Set.empty Set.empty

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
      -- TODO: What happens when HereMarker is in the second or third term?
      -- TODO: maybe do something smarter, so that term2 isn't typechecked
      -- twice and since if a proof is t1 t2 t3, the returning list will
      -- be (t1, t2), (t2', t3), (t3', t4)
      -- make sure that t2 and t2' point to the same values.
      -- TODO: HereMarker ($)
      checkSteps1 :: [UT.ProofStep] -> CheckM T.SubProof
      checkSteps1 ((UT.PSCmd transCmd):(UT.PSImpRel imprel):[]) = do
        -- Replace first term with start and last term with goal.
        tStart <- gets start
        shownStart <- removeImplicitLet tStart
        tTransCmd <- check transCmd
        tImprel <- check imprel
        tEnd <- gets goal
        return $ [T.PSMiddle tStart tTransCmd tImprel tEnd]

      -- | Given
      -- - a transformational command
      -- - The previous shown term
      --Returns the context that the transformational command should be
      --applied to.
      --Status: Currently only works if the context is supplied explicitly
      --via an argument. Later, it may also work by matching subterms on the
      --term or similar.
      getContext :: UT.TransCmd -> T.Term -> CheckM T.Term
      getContext (UT.CmdSpecial UT.STCAlphaEquiv) _ = return T.THole
      getContext (UT.CmdGeneral _name argList) _ = undefined

      {-
      checkSteps1 ((UT.PSCmd transCmd)
                   :(UT.PSImpRel imprel)
                   :(UT.PSTerm term2)
                   :cmds) = do
        -- If first term is not specified, substitute for the start term. note
        -- that this doesn't work in the inductive case.
        startTerm <- gets start
        startTermRaw <- removeImplicitLet startTerm
        tTransCmd <- check transCmd
        tSubterm <- getSubTerm subterm startTermRaw
        tImprel <- check imprel
        tTerm2 <- withLetContext =<< check term2
        let proofStep = T.PSMiddle startTerm tSubterm tTransCmd tImprel tTerm2
        proofSteps <- checkSteps2 $ (UT.PSTerm term2):cmds
        return $ proofStep:proofSteps
      checkSteps1 steps = checkSteps2 steps

      checkSteps2 :: [UT.ProofStep] -> CheckM T.SubProof
      checkSteps2 [] = return []
      checkSteps2 ((UT.PSTerm term1)
                     :(UT.PSCmd transCmd)
                     :(UT.PSImpRel imprel)
                     :(UT.PSTerm term2)
                     :cmds) = do
        proofStep <- checkProofStep term1 subterm transCmd imprel term2
        proofSteps <- checkSteps2 $ (UT.PSTerm term2):cmds
        return $ proofStep:proofSteps
      checkSteps2 ((UT.PSTerm term1)
                   :(UT.PSCmd transCmd)
                   :(UT.PSImpRel impRel)
                   :[]) = do
        -- If the last term is skipped, the last term is implicitly the goal,
        -- so we put it after. Note that the last improvement relation is
        -- still needed (at least at this stage)
        tTerm1 <- check term1
        tTerm1wCtx <- withLetContext tTerm1
        tSubterm <- getSubTerm subterm tTerm1
        tTransCmd <- check transCmd
        tImpRel <- check impRel
        tTerm2wCtx <- gets goal
        let proofStep = T.PSMiddle tTerm1wCtx
                                   tSubterm
                                   tTransCmd
                                   tImpRel
                                   tTerm2wCtx
        return [proofStep]
      checkSteps2 ((UT.PSTerm _ ):[]) = return []
                   --The last term is in the next-to-last proof step too, so
                   --it is not lost.
      checkSteps2 _ = fail $ "Ordering of proof steps are invalid. Every other "
        ++"step must be a term and every other a transformational command "
        ++"and an improvement relation. Note that the HereMarker $ is not "
        ++"supported yet."

      checkProofStep :: UT.Term -> UT.SubTerm -> UT.TransCmd -> UT.ImpRel
                        -> UT.Term -> CheckM T.ProofStep
      checkProofStep term1 subterm transCmd imprel term2 = do
        tTerm1 <- check term1
        tTerm1withCtx <- withLetContext tTerm1
        command <- check transCmd
        tSubTerm <- getSubTerm subterm tTerm1
        tImprel <- check imprel
        tTerm2 <- check term2
        tTerm2withCtx <- withLetContext tTerm2
        let proofStep = T.PSMiddle tTerm1withCtx
                                   tSubTerm
                                   command
                                   tImprel
                                   tTerm2withCtx
        return proofStep
        -}
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
  type TypedVersion UT.ImpRel = Com.ImpRel
  check UT.DefinedEqual        = return Com.DefinedEqual
  check UT.StrongImprovementLR = fail "not implemented yet 22.1"
  check UT.WeakImprovementLR   = fail "not implemented yet 23"
  check UT.StrongImprovementRL = fail "not implemented yet 24"
  check UT.WeakImprovementRL   = fail "not implemented yet 25"
  check UT.StrongCostEquiv     = fail "not implemented yet 26"
  check UT.WeakCostEquiv       = fail "not implemented yet 27"

instance Checkable UT.TransCmd where
  type TypedVersion UT.TransCmd = T.Command
  check (UT.CmdSpecial UT.STCAlphaEquiv) = return T.AlphaEquiv
  check (UT.CmdGeneral cmdName args)  = fail "not implemented yet 30"

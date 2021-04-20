{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module MiniTypeChecker (typecheckProof, checkTypedTerm) where

import qualified AbsSie as UT
import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import qualified Common as Com (ImpRel(..))

import Data.Text (pack)
import qualified Control.Monad.Logger as Log
import Data.List.Extra (firstJust)
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.State (StateT, runStateT, gets, MonadState, modify)
import Control.Monad.Extra (firstJustM)
import Data.Functor.Identity (Identity, runIdentity)

import ShowTypedTerm (showTypedTerm)
import TermCorrectness (checkTypedTerm, numHoles, checkBoundVariablesDistinct
                       , checkFreeVars, getBoundVariables, isValue)
import ToLocallyNameless (toLocallyNameless)
import qualified TypedLawAST as Law
import OtherUtils (assert, assertTerm, noSupport)
import CheckMonad (CheckM, runCheckM)

data MySt = MkSt {letContext :: Maybe T.LetBindings
                 , start :: T.Term
                 , goal :: T.Term
                 , freeVarVars :: Set.Set String
                 , lawMap :: Law.LawMap
                 }

mkInitSt :: Law.LawMap -> MySt
mkInitSt lawMap = MkSt {letContext = undefined
                       , start= undefined
                       , goal = undefined
                       , freeVarVars = undefined
                       , lawMap = lawMap
                       }

newtype StCheckM a = Mk {getM :: (StateT MySt CheckM a)}
  deriving (Functor, Applicative, Monad, MonadState MySt, MonadError String
            , Log.MonadLogger)

instance MonadFail StCheckM where
    fail str = throwError str

typecheckProof :: UT.ProofScript -> Law.LawMap -> Either String T.ProofScript
typecheckProof proofScript lawMap =
  let initSt = mkInitSt lawMap
  in runStCheckM initSt $ check proofScript

runStCheckM :: MySt -> StCheckM a -> Either String a
runStCheckM initSt monadic = do
  let res = runCheckM $
              (flip runStateT) initSt $
                  getM monadic

  case res of
    Left errorMsgs -> let combined = intercalate "\n" errorMsgs
                      in Left combined
    Right (a, _st) -> Right a

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
withLetContext :: T.Term -> StCheckM T.Term
withLetContext startTerm = do
  context <- gets letContext
  case context of
    Nothing -> return startTerm
    Just letBindings -> return $ T.TLet letBindings startTerm

-- | the inverse of withLetContext
removeImplicitLet :: T.Term -> StCheckM T.Term
removeImplicitLet startTerm = do
  context <- gets letContext
  case context of
    Nothing -> return startTerm
    Just _ -> case startTerm of
      T.TLet _ inner -> return inner
      _ -> fail "internal: Tried to remove implicit let but there is none."

-- Checks correctness of a
class Checkable a where
  type TypedVersion a
  check :: a -> StCheckM (TypedVersion a)

-- Just transforms a to its typed version
class Transformable a where
  type TransformedVersion a
  transform :: a -> StCheckM (TransformedVersion a)

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
    let T.DFreeVars termVars varVars = tFreeVars
    modify (\st -> st{freeVarVars = varVars})
    tStart <- checkTopLevelTerm start
    tGoal <- checkTopLevelTerm goal
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

-- | Checks a term, which consists of the following:
-- - Converts to T.Term.
-- - Adds the implicit let of derivations in context (if there is one)
-- - Stack weight expressions: See checkWeightExpr
checkTopLevelTerm :: UT.Term -> StCheckM T.Term
checkTopLevelTerm term = do
  transformed <- transform term
  withLet <- withLetContext transformed
  expectedFreeVars <- gets freeVarVars
  checkTypedTerm withLet expectedFreeVars
  return withLet

instance Transformable UT.Term where
  type TransformedVersion UT.Term = T.Term
  transform :: UT.Term -> StCheckM T.Term
  transform (UT.TAny)                          = fail "not implemented yet 3"
  transform (UT.TTermVar capitalIdent)         = fail "not implemented yet 4"
  transform (UT.TNonTerminating)               = fail "not implemented yet 5"
  transform (UT.TVar var)                      = do
    let tVar = getVarName var
    return $ T.TVar tVar
  transform (UT.TIndVar var indExpr)           = fail "not implemented yet 6"
  transform (UT.TNum integer)                  = return $ T.TNum integer
  transform (UT.THole)                         = return T.THole
  transform (UT.TConstructor constructor)      = fail "not implemented yet 7"
  transform (UT.TLam var term)                 = do
    let tVar = getVarName var
    tTerm <- transform term
    return $ T.TLam tVar tTerm
  transform (UT.TLet letBindings term)         = do
    tLetBindings <- transform letBindings
    tTerm <- transform term
    return $ T.TLet tLetBindings tTerm
  transform (UT.TStackSpike term)              = fail "not implemented yet 8"
  transform (UT.TStackSpikes stackWeight term) = fail "not implemented yet 9"
  transform (UT.THeapSpike term)               = fail "not implemented yet 10"
  transform (UT.THeapSpikes heapWeight term)   = fail "not implemented yet 11"
  transform (UT.TDummyBinds varSet term)       = do
    tVarSet <- transform varSet
    tTerm <- transform term
    return $ T.TDummyBinds tVarSet tTerm
  transform (UT.TRApp term var) = do
    tTerm <- transform term
    let tVar = getVarName var
    return $ T.TRedWeight 1 $ T.RApp tTerm tVar
  transform (UT.TRAppW redWeight term var) = noSupport "TRAppW"
  transform (UT.TRPlus term1 term2) =
    transformPlus Nothing term1 Nothing term2
  transform (UT.TRPlusW1 redWeight term1 term2) =
    transformPlus (Just redWeight) term1 Nothing term2
  transform (UT.TRPlusW2 term1 redWeight term2) =
    transformPlus Nothing term1 (Just redWeight) term2
  transform (UT.TRPlusWW redWeight1 term1 redWeight2 term2) =
    transformPlus (Just redWeight1) term1 (Just redWeight2) term2
  transform (UT.TRCase maybeRedWeight term caseStms) = noSupport "TRCase"
  transform (UT.TRAddConst maybeRedWeight integer term) = noSupport "TRAddConst"
  transform (UT.TRIsZero maybeRedWeight term) = noSupport "TRIsZero"
  transform (UT.TRSeq maybeRedWeight term1 term2) = noSupport "TRSeq"

transformPlus :: Maybe UT.RedWeight
                 -> UT.Term
                 -> Maybe UT.RedWeight
                 -> UT.Term
                 -> StCheckM T.Term
transformPlus rw1 t1 rw2 t2 = do
  trans1 <- transform t1
  trans2 <- transform t2
  case (rw1, rw2) of
    (Nothing, Nothing) ->
      return $ T.TRedWeight 1 $ T.RPlusWeight trans1 1 trans2
    _ -> fail "not implemented yet: weights on Plus"

instance Transformable UT.LetBindings where
  type TransformedVersion UT.LetBindings = T.LetBindings
  transform UT.LBSAny = fail "not implemented yet 12"
  transform (UT.LBSVar capitalIdent) = fail "not implemented yet"
  transform (UT.LBSSet bindingSetList) = do
    tLetBindings <- mapM transformSingle bindingSetList
    return tLetBindings
    where
      transformSingle :: UT.LetBinding
                     -> StCheckM (T.Name, T.StackWeight, T.HeapWeight, T.Term)
      transformSingle UT.LBAny = fail "not implemented yet 13"
      transformSingle (UT.LBConcrete var UT.BSNoWeight term) = do
        let tVar = getVarName var
        tTerm <- transform term
        return (tVar, 1,1, tTerm)
      transformSingle (UT.LBConcrete var withWeight term) =
        fail "not implemented yet 14"


instance Transformable UT.VarSet where
  type TransformedVersion UT.VarSet = T.VarSet
  transform (UT.DVarSet vars) = do
    let tVars = map getVarName vars
    return $ Set.fromList tVars

getVarName :: UT.Var -> String
getVarName (UT.DVar (UT.Ident name)) = name

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
      checkSteps1 :: [UT.ProofStep] -> StCheckM T.SubProof
      checkSteps1 ((UT.PSCmd transCmd):(UT.PSImpRel imprel):[]) = do
        -- Replace first term with start and last term with goal.
        tStart <- gets start
        tTransCmd <- check transCmd
        tImprel <- check imprel
        tEnd <- gets goal
        return $ [T.PSMiddle tStart tTransCmd tImprel tEnd]
      checkSteps1 ((UT.PSCmd transCmd)
                   :(UT.PSImpRel imprel)
                   :(UT.PSTerm term2)
                   :cmds) = do
        -- If first term is not specified, substitute for the start term. note
        -- that this doesn't work in the inductive case.
        startTerm <- gets start
        tTransCmd <- check transCmd
        tImprel <- check imprel
        tTerm2 <- checkTopLevelTerm term2
        let proofStep = T.PSMiddle startTerm tTransCmd tImprel tTerm2
        proofSteps <- checkSteps2 $ (UT.PSTerm term2):cmds
        return $ proofStep:proofSteps
      checkSteps1 steps = checkSteps2 steps

      checkSteps2 :: [UT.ProofStep] -> StCheckM T.SubProof
      checkSteps2 [] = return []
      checkSteps2 ((UT.PSTerm term1)
                     :(UT.PSCmd transCmd)
                     :(UT.PSImpRel imprel)
                     :(UT.PSTerm term2)
                     :cmds) = do
        proofStep <- checkProofStep term1 transCmd imprel term2
        proofSteps <- checkSteps2 $ (UT.PSTerm term2):cmds
        return $ proofStep:proofSteps
      checkSteps2 ((UT.PSTerm term1)
                   :(UT.PSCmd transCmd)
                   :(UT.PSImpRel impRel)
                   :[]) = do
        -- If the last term is skipped, the last term is implicitly the goal,
        -- so we put it after. Note that the last improvement relation is
        -- still needed (at least at this stage)
        tTerm1 <- checkTopLevelTerm term1
        tTransCmd <- check transCmd
        tImpRel <- check impRel
        tTerm2 <- gets goal
        let proofStep = T.PSMiddle tTerm1 tTransCmd tImpRel tTerm2
        return [proofStep]
      checkSteps2 ((UT.PSTerm _ ):[]) = return []
                   --The last term is in the next-to-last proof step too, so
                   --it is not lost.
      checkSteps2 _ = fail $ "Ordering of proof steps are invalid. Every other "
        ++"step must be a term and every other a transformational command "
        ++"and an improvement relation. Note that the HereMarker $ is not "
        ++"supported yet."

      checkProofStep :: UT.Term -> UT.TransCmd -> UT.ImpRel
                        -> UT.Term -> StCheckM T.ProofStep
      checkProofStep term1 transCmd imprel term2 = do
        tTerm1 <- checkTopLevelTerm term1
        command <- check transCmd
        tImprel <- check imprel
        tTerm2 <- checkTopLevelTerm term2
        let proofStep = T.PSMiddle tTerm1 command tImprel tTerm2
        return proofStep
  check (UT.PGeneral commandName cmdArgs subProofs UT.DQed) =
    fail "not implemented yet 20"

instance Checkable UT.ImpRel where
  type TypedVersion UT.ImpRel = Com.ImpRel
  check UT.DefinedEqual        = return Com.DefinedEqual
  check UT.StrongImprovementLR = return Com.StrongImprovementLR
  check UT.WeakImprovementLR   = return Com.WeakImprovementLR
  check UT.StrongImprovementRL = fail "not implemented yet 24"
  check UT.WeakImprovementRL   = fail "not implemented yet 25"
  check UT.StrongCostEquiv     = return Com.StrongCostEquiv
  check UT.WeakCostEquiv       = return Com.WeakCostEquiv

instance Checkable UT.TransCmd where
  type TypedVersion UT.TransCmd = T.Command
  check (UT.CmdSpecial UT.STCAlphaEquiv) = return T.AlphaEquiv
  check (UT.CmdGeneral (UT.CommandName commandName) args)  = do
    laws <- gets lawMap
    case Map.lookup commandName laws of
      Nothing -> throwError $ "The law "++commandName++" does not correspond "
                   ++"to a law in the law file."
      Just law -> do
        Log.logInfoN . pack $ "Checking arguments to transformation "
                              ++commandName
        context <- getContext args
        checkedMaybeArgs <- mapM checkArg args
        let checkedArgs = catMaybes checkedMaybeArgs
            substitutions = Map.fromList checkedArgs
        return $ T.Law context law substitutions

instance Checkable UT.IntExpr where
  type TypedVersion UT.IntExpr = T.IntExpr
  check (UT.IEAny) = noSupport "IEAny"
  check (UT.IEVar _) = noSupport "IEVar"
  check (UT.IENum integer) = return $ T.IENum integer
  check (UT.IEPlus _ _) = noSupport "IEPlus"
  check (UT.IEMinus _ _) = noSupport "IEMinus"

getContext :: [UT.CmdArgument] -> StCheckM T.Term
getContext args = do
  case firstJust getCtx args of
    Just utCtx -> do
      transCtx <- transform utCtx
      checkBoundVariablesDistinct transCtx
      assert (numHoles transCtx == 1) $ "The context should contain exactly "
        ++"one hole, for context "++showTypedTerm transCtx
      -- Since the context should be with respect to the whole term, we should
      -- be able to check free variables
      expectedFreeVars <- gets freeVarVars
      checkFreeVars transCtx expectedFreeVars
      return transCtx
    Nothing -> throwError $ "The law does not specify the context that it is applied in. SIE is currently not able to guess that."
  where
    getCtx :: UT.CmdArgument -> Maybe UT.Term
    getCtx (UT.CAAssignGeneral assignee value) = case assignee of
      UT.CAOtherMetaVar _ -> Nothing
      UT.CASubTerm -> case value of
        UT.CVSubTerm UT.STWholeWithCtx -> Just UT.THole
        _ -> Nothing
      UT.CAContext -> case value of
        UT.CVSubTerm (UT.STTerm term) -> Just term
        _ -> Nothing
    getCtx _ = Nothing


checkArg :: UT.CmdArgument -> StCheckM (Maybe (String, T.Substitute))
checkArg (UT.CAValue _) = noSupport "CAValue"
checkArg (UT.CAAssignInt (UT.MVIntegerVar name) intExpr) = do
  Log.logInfoN . pack $ "Checking argument "++name
  tIntExpr <- check intExpr
  return $ Just (name, T.SIntegerVar tIntExpr)
checkArg (UT.CAAssignLet (UT.MVLetBindings name) letBindings) = do
  Log.logInfoN . pack $ "Checking argument "++name
  transLet <- transform letBindings
  let inTerm = T.TLet transLet (T.TNum 1)
  checkArgumentTerm inTerm
  assert (numHoles inTerm == 0) "Argument should not be a context."
  return $ Just (name, T.SLetBindings transLet)
checkArg (UT.CAAssignGeneral assignee value) = case assignee of
  UT.CASubTerm -> return Nothing
  UT.CAContext -> return Nothing
  UT.CAOtherMetaVar metaVar -> case metaVar of
    UT.OtherMetaVarMVValue (UT.MVValue name) -> do
      logCheckArg name
      case value of
        UT.CVSubTerm (UT.STTerm term) -> do
          tTerm <- transform term
          assertTerm (isValue tTerm) "should be a value" tTerm
          checkArgumentTerm tTerm
          assert (numHoles tTerm == 0) "Argument should not be a context"
          return $ Just (name, T.SValue tTerm)
        UT.CVSubTerm _ -> noSupport "non-explicit subterm"
        _ -> throwError $ "value for "++name++" is not a term"
    UT.OtherMetaVarMVContext (UT.MVContext name) -> do
      logCheckArg name
      case value of
        UT.CVSubTerm (UT.STTerm utCtx) -> do
          tCtx <- transform utCtx
          Log.logInfoN . pack $ "Checking the value; "++showTypedTerm tCtx
          checkArgumentTerm tCtx
          assert (numHoles tCtx > 0) "Argument should be a context."
          return $ Just (name, T.SContext tCtx)
        _ -> throwError "Not a context."
    UT.OtherMetaVarMVVar (UT.MVVar name) -> do
      logCheckArg name
      case value of
        UT.CVSubTerm (UT.STTerm (UT.TVar (UT.DVar (UT.Ident varName)))) ->
          return $ Just (name, T.SVar varName)
        _ -> throwError "Not a variable"
    UT.OtherMetaVarMVVarVect (UT.MVVarVect name) -> noSupport "MVVarVect"
    UT.OtherMetaVarMVValueContext (UT.MVValueContext name) -> noSupport "MVValueContext"
    UT.OtherMetaVarMVReduction (UT.MVReduction name) -> noSupport "MVReduction"
    UT.OtherMetaVarMVVarSet (UT.MVVarSet name) -> do
      logCheckArg name
      case value of
        UT.CVVarSet (UT.DVarSet varList) ->
          let strList = map getVarName varList
              strSet = Set.fromList strList
          in return $ Just (name, T.SVarSet strSet)
        _ -> throwError "Not a set of variables"
    UT.OtherMetaVarMVTerm (UT.MVTerm name) -> noSupport "MVTerm"
    UT.OtherMetaVarMVPattern (UT.MVPattern name) -> noSupport "MVPattern"
    UT.OtherMetaVarMVCaseStm (UT.MVCaseStm name) -> noSupport "MVCaseStm"
    UT.OtherMetaVarMVConstructorName (UT.MVConstructorName name) -> noSupport "MVConstructorName"
    where
      logCheckArg name = Log.logInfoN . pack $ "Checking argument "++name

checkArgumentTerm :: T.Term -> StCheckM ()
checkArgumentTerm term = do
  checkBoundVariablesDistinct term
  declaredFree <- gets freeVarVars
  let boundVars = getBoundVariables term
  assert (declaredFree `Set.disjoint` declaredFree) $ "argument cannot "
    ++"bind declared free variables."

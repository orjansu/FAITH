{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module MiniTypeChecker (typecheckProof, checkTypedTerm) where

import qualified ParSieLaws (pMetaVar, myLexer)
import qualified AbsSieLaws as UTLaw
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
import GHC.Stack (HasCallStack)
import GHC.Base (maxInt)
import qualified Prelude.SafeEnum as Safe (fromEnum)

import ShowTypedTerm (showTypedTerm)
import TermCorrectness (checkTypedTerm, numHoles, checkBoundVariablesDistinct
  , checkFreeVars, getBoundVariables, isValue, getAllMetaVars)
import ToLocallyNameless (toLocallyNameless)
import CheckMonad (CheckM, runCheckM, assert, assertTerm, noSupport
                  , throwCallstackError)
import LanguageLogic (nilName, consName, trueName, falseName)

data MySt = MkSt { letBindings :: Map.Map String T.LetBindings
                 , constructors :: Map.Map String Int
                 , letContext :: Maybe T.LetBindings
                 , start :: T.Term
                 , goal :: T.Term
                 , freeVarVars :: Set.Set String
                 , lawMap :: Law.LawMap
                 }

mkInitSt :: Law.LawMap -> MySt
mkInitSt lawMap = MkSt { letBindings = Map.empty
                       , constructors = Map.fromList [(nilName, 0)
                                                     , (consName, 2)
                                                     , (trueName, 0)
                                                     , (falseName, 0)]
                       , letContext = undefined
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

typecheckProof :: (HasCallStack) =>
                  UT.ProofScript -> Law.LawMap -> Either String T.ProofScript
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
removeImplicitLet :: HasCallStack => T.Term -> StCheckM T.Term
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
  check :: HasCallStack => a -> StCheckM (TypedVersion a)

-- Just transforms a to its typed version
class Transformable a where
  type TransformedVersion a
  transform :: HasCallStack => a -> StCheckM (TransformedVersion a)

instance Checkable UT.ProofScript where
  type TypedVersion UT.ProofScript = T.ProofScript
  check (UT.DProofScript (UT.DProgBindings bindings) theorems) = do
    mapM addEntry bindings
    tTheorems <- mapM check theorems
    return $ T.DProofScript tTheorems
    where
      -- Correctness properties on the let bindings will be
      -- enforced when inserted into the terms. Unused bindings will not be
      -- checked, but that's fine.
      addEntry :: UT.ProgBinding -> StCheckM ()
      addEntry (UT.PBLet (UT.CapitalIdent name) utLetBinds) = do
        tLetBindings <- transform utLetBinds
        letBindings1 <- gets letBindings
        let letBindings2 = Map.insert name tLetBindings letBindings1
        modify (\st -> st{letBindings = letBindings2})
      addEntry (UT.PBConstructor (UT.CapitalIdent name) numArgs) = do
        constructors1 <- gets constructors
        safeNumArgs <- case Safe.fromEnum numArgs of
          Just n -> return n
          Nothing -> throwError $ "There is no support for constructors with "
            ++"more than "++show maxInt++" number of arguments."
        let constructors2 = Map.insert name safeNumArgs constructors1
        modify (\st -> st{constructors = constructors2})

instance Checkable UT.Theorem where
  type TypedVersion UT.Theorem = T.Theorem
  check (UT.DTheorem (UT.DProposition context
                                       freeVars
                                       start
                                       impRel
                                       goal) proof) = do
    letContext <- case context of
      UT.WithContext (UT.CapitalIdent ctxVar) -> do
        letBindings1 <- gets letBindings
        case Map.lookup ctxVar letBindings1 of
          Just letCtx -> return $ Just letCtx
          Nothing -> throwError $ "Context "++ctxVar++" was specified but does "
                      ++"not correspond to a binding."
      UT.NoContext -> return Nothing
    modify (\st -> st{letContext = letContext})
    tFreeVars <- check freeVars
    let T.DFreeVars termVars varVars = tFreeVars
    modify (\st -> st{freeVarVars = varVars})
    tStart <- checkTopLevelTerm start
    tGoal <- checkTopLevelTerm goal
    modify (\st -> st{start = tStart, goal = tGoal})
    tProof <- check proof
    tImpRel <- check impRel
    let prop = T.DProposition tFreeVars tStart tImpRel tGoal
    return $ T.DTheorem prop tProof

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
  transform (UT.TAny)                          = noSupport "TAny"
  transform (UT.TTermVar capitalIdent)         = noSupport "TTermVar"
  transform (UT.TNonTerminating)               = return T.TNonTerminating
  transform (UT.TVar var)                      = do
    let tVar = getVarName var
    return $ T.TVar tVar
  transform (UT.TIndVar var indExpr)           = noSupport "TIndVar"
  transform (UT.TNum integer)                  = return $ T.TNum integer
  transform (UT.THole)                         = return T.THole
  transform (UT.TConstructor constructor)      = do
    (name, args) <- transform constructor
    return $ T.TConstructor name args
  transform (UT.TLam var term)                 = do
    let tVar = getVarName var
    tTerm <- transform term
    return $ T.TLam tVar tTerm
  transform (UT.TLet letBindings term)         = do
    tLetBindings <- transform letBindings
    tTerm <- transform term
    return $ T.TLet tLetBindings tTerm
  transform (UT.TStackSpike term)              = do
    tTerm <- transform term
    return $ T.TStackSpikes 1 tTerm
  transform (UT.TStackSpikes (UT.StackWeightExpr sw) term) = do
    tTerm <- transform term
    return $ T.TStackSpikes sw tTerm
  transform (UT.THeapSpike term)               = do
    tTerm <- transform term
    return $ T.THeapSpikes 1 tTerm
  transform (UT.THeapSpikes (UT.HeapWeightExpr hw) term)   = do
    tTerm <- transform term
    return $ T.THeapSpikes hw tTerm
  transform (UT.TDummyBinds varSet term)       = do
    tVarSet <- transform varSet
    tTerm <- transform term
    return $ T.TDummyBinds tVarSet tTerm
  transform (UT.TRApp term var) = do
    tTerm <- transform term
    let tVar = getVarName var
    return $ T.TRedWeight 1 $ T.RApp tTerm tVar
  transform (UT.TRAppW (UT.DRedWeight (UT.StackWeightExpr redWeight))
                       term
                       var) = do
    tTerm <- transform term
    let varName = getVarName var
    return $ T.TRedWeight redWeight $ T.RApp tTerm varName
  transform (UT.TRAppNoW term var) = do
    tTerm <- transform term
    let tVar = getVarName var
    return $ T.TRedWeight 0 $ T.RApp tTerm tVar
  transform (UT.TRPlus term1 term2) =
    transformPlus Nothing term1 Nothing term2
  transform (UT.TRPlusW1 redWeight term1 term2) =
    transformPlus (Just redWeight) term1 Nothing term2
  transform (UT.TRPlusW2 term1 redWeight term2) =
    transformPlus Nothing term1 (Just redWeight) term2
  transform (UT.TRPlusWW redWeight1 term1 redWeight2 term2) =
    transformPlus (Just redWeight1) term1 (Just redWeight2) term2
  transform (UT.TRCase maybeRedWeight term caseStms) = do
    rw <- transform maybeRedWeight
    tTerm <- transform term
    alts <- mapM transform caseStms
    return $ T.TRedWeight rw $ T.RCase tTerm alts
  transform (UT.TRAddConst maybeRedWeight integer term) = do
    rw <- transform maybeRedWeight
    tTerm <- transform term
    return $ T.TRedWeight rw $ T.RAddConst integer tTerm
  transform (UT.TRIsZero maybeRedWeight term) = do
    rw <- transform maybeRedWeight
    tTerm <- transform term
    return $ T.TRedWeight rw $ T.RIsZero tTerm
  transform (UT.TRSeq maybeRedWeight term1 term2) = do
    rw <- transform maybeRedWeight
    tTerm1 <- transform term1
    tTerm2 <- transform term2
    return $ T.TRedWeight rw $ T.RSeq tTerm1 tTerm2

transformPlus :: Maybe UT.RedWeight
                 -> UT.Term
                 -> Maybe UT.RedWeight
                 -> UT.Term
                 -> StCheckM T.Term
transformPlus mrw1 t1 mrw2 t2 = do
  trans1 <- transform t1
  trans2 <- transform t2
  let rw1 = toWeight mrw1
      rw2 = toWeight mrw2
  return $ T.TRedWeight rw1 $ T.RPlusWeight trans1 rw2 trans2
  where
    toWeight :: Maybe UT.RedWeight -> Integer
    toWeight Nothing = 1
    toWeight (Just (UT.DRedWeight (UT.StackWeightExpr n))) = n


instance Transformable UT.LetBindings where
  type TransformedVersion UT.LetBindings = T.LetBindings
  transform UT.LBSAny = fail "not implemented yet 12"
  transform (UT.LBSVar (UT.CapitalIdent name)) = do
    letBindings <- gets letBindings
    case Map.lookup name letBindings of
      Just letBinds -> return letBinds
      Nothing -> throwError $ "LetBinding "++name++" not declared."
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
      transformSingle (UT.LBConcrete var withWeight term) = do
        let UT.BSWeights (UT.StackWeightExpr sw)
                         (UT.HeapWeightExpr hw) = withWeight
            varName = getVarName var
        tTerm <- transform term
        return (varName, sw, hw, tTerm)

instance Transformable UT.CaseStm where
  type TransformedVersion UT.CaseStm = (String, [String], T.Term)
  transform (UT.CSConcrete constructor term) = do
    (name, args) <- transform constructor
    tTerm <- transform term
    return (name, args, tTerm)

instance Transformable UT.VarSet where
  type TransformedVersion UT.VarSet = T.VarSet
  transform (UT.DVarSet vars) = do
    let tVars = map getVarName vars
    return $ Set.fromList tVars

getVarName :: UT.Var -> String
getVarName (UT.DVar (UT.Ident name)) = name

instance Transformable UT.MaybeRedWeight where
  type TransformedVersion UT.MaybeRedWeight = Integer
  transform (UT.WithRedWeight (UT.DRedWeight (UT.StackWeightExpr int))) =
    return int
  transform UT.NoRedWeight = return 1

instance Transformable UT.Constructor where
  type TransformedVersion UT.Constructor = (String, [String])
  transform = \case
    UT.CGeneralWArgs (UT.ConstructorName name) vars
      -> checkConstructor name vars
    UT.CGeneralNoArgs (UT.ConstructorName name) -> checkConstructor name []
    UT.CCons var1 var2 -> return $ (consName, [getVarName var1
                                              , getVarName var2])
    where
      checkConstructor name vars = do
        constructors <- gets constructors
        case Map.lookup name constructors of
          Just numArgs -> do
            actualNumArgs <- case Safe.fromEnum (length vars) of
              Just n -> return n
              Nothing -> throwCallstackError $ "We do not support constructors "
                ++"more than "++show maxInt++" arguments."
            assert (actualNumArgs == numArgs) $ "All constructors must be fully "
              ++"applied, so "++show name++" must have "++show numArgs
              ++" arguments."
            let varNames = map getVarName vars
            return (name, varNames)
          Nothing -> throwError $ "Constructor "++name++" is not declared. "
            ++"If it has "++show(length vars)++" arguments, declare it by typing "
            ++name++" ("++show(length vars)++"); in the bindings list."

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
        checkAllSubstitutionsProvided law substitutions
        return $ T.Law context law substitutions

getContext :: HasCallStack => [UT.CmdArgument] -> StCheckM T.Term
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
    getCtx (UT.CAAssign assignee value) = case assignee of
      UT.CAMetaVar _ -> Nothing
      UT.CASubTerm -> case value of
        UT.CVSubTerm UT.STWholeWithCtx -> Just UT.THole
        _ -> Nothing
      UT.CAContext -> case value of
        UT.CVSubTerm (UT.STTerm term) -> Just term
        _ -> Nothing
    getCtx _ = Nothing


checkArg :: HasCallStack => UT.CmdArgument
                            -> StCheckM (Maybe (String, T.Substitute))
checkArg (UT.CAValue _) = noSupport "CAValue"
checkArg (UT.CAAssign assignee value) = case assignee of
  UT.CASubTerm -> return Nothing
  UT.CAContext -> return Nothing
  UT.CAMetaVar metaVar -> do
    let mvStr = case metaVar of
                  UT.BigVar (UT.CapitalIdent str) -> str
                  UT.SmallVar (UT.Ident str) -> str
    logCheckArg mvStr
    parMV <- case (ParSieLaws.pMetaVar (ParSieLaws.myLexer mvStr)) of
               Left err -> throwError $ "Error when parsing metavariable: "++err
               Right parsed -> return parsed
    case parMV of
      UTLaw.MetaVarMVLetBindings (UTLaw.MVLetBindings name) -> case value of
        UT.CVLet letBindings -> do
          transLet <- transform letBindings
          let inTerm = T.TLet transLet (T.TNum 1)
          checkArgumentTerm inTerm
          assert (numHoles inTerm == 0) "Argument should not be a context."
          return $ Just (name, T.SLetBindings transLet)
        _ -> throwError $ "argument for "++mvStr++" is not a let-binding."
      UTLaw.MetaVarMVValue (UTLaw.MVValue name) -> do
        case value of
          UT.CVSubTerm (UT.STTerm term) -> do
            tTerm <- transform term
            assertTerm (isValue tTerm) "should be a value" tTerm
            checkArgumentTerm tTerm
            assert (numHoles tTerm == 0) "Argument should not be a context"
            return $ Just (name, T.SValue tTerm)
          UT.CVSubTerm _ -> noSupport "non-explicit subterm"
          _ -> throwError $ "value for "++name++" is not a term"
      UTLaw.MetaVarMVContext (UTLaw.MVContext name) -> do
        case value of
          UT.CVSubTerm (UT.STTerm utCtx) -> do
            tCtx <- transform utCtx
            Log.logInfoN . pack $ "Checking the value; "++showTypedTerm tCtx
            checkArgumentTerm tCtx
            assert (numHoles tCtx > 0) "Argument should be a context."
            return $ Just (name, T.SContext tCtx)
          _ -> throwError "Not a context."
      UTLaw.MetaVarMVIntegerVar (UTLaw.MVIntegerVar name) ->
        case value of
          UT.CVIntExpr integer -> do
            return $ Just (name, T.SIntegerVar integer)
          _ -> throwError $ "Argument "++mvStr++" is not an integer "
                ++"expression. Use int ( Term ) to indicate that it is."
      UTLaw.MetaVarMVVar (UTLaw.MVVar name) -> do
        case value of
          UT.CVSubTerm (UT.STTerm (UT.TVar (UT.DVar (UT.Ident varName)))) ->
            return $ Just (name, T.SVar varName)
          _ -> throwError "Not a variable"
      UTLaw.MetaVarMVVarVect (UTLaw.MVVarVect name) ->
        case value of
          UT.CVVarVect vars -> do
            let tVars = map getVarName vars
            return $ Just $ (name, T.SVarVect tVars)
          _ -> throwError "Not a vector of variables."
      UTLaw.MetaVarMVValueContext (UTLaw.MVValueContext name) ->
        case value of
          UT.CVSubTerm (UT.STTerm vctx) -> do
            tVctx <- transform vctx
            checkArgumentTerm tVctx
            assert (numHoles tVctx > 0) "Argument should be a context."
            assert (isValue tVctx) "Argument should be a value."
            return $ Just $ (name, T.SValueContext tVctx)
          _ -> throwError "Not a value context."
      UTLaw.MetaVarMVReduction (UTLaw.MVReduction name) ->
        case value of
          UT.CVSubTerm (UT.STTerm term) -> do
            tTerm <- transform term
            assert (isReductionContext tTerm) $ "Argument should be a reduction"
              ++"context."
            T.TRedWeight rw red <- return tTerm
            return $ Just $ (name, T.SReduction rw red)
          _ -> throwError "Not a reduction context"
      UTLaw.MetaVarMVVarSet (UTLaw.MVVarSet name) -> do
        case value of
          UT.CVVarSet (UT.DVarSet varList) ->
            let strList = map getVarName varList
                strSet = Set.fromList strList
            in return $ Just (name, T.SVarSet strSet)
          _ -> throwError "Not a set of variables"
      UTLaw.MetaVarMVTerm (UTLaw.MVTerm name) ->
        case value of
          UT.CVSubTerm (UT.STTerm term) -> do
            tTerm <- transform term
            checkArgumentTerm tTerm
            assert (numHoles tTerm == 0) "Should not be a context."
            return $ Just (name, T.STerm tTerm)
          _ -> throwError "Not a term"
      UTLaw.MetaVarMVTerms (UTLaw.MVTerms name) ->
        case value of
          UT.CVTerms utTerms -> do
            tTerms <- mapM go utTerms
            return $ Just (name, T.STerms tTerms)
          _ -> throwError "not terms"
        where
          go utTerm = do
            tTerm <- transform utTerm
            checkArgumentTerm tTerm
            assert (numHoles tTerm == 0) "Should not be a context."
            return tTerm
      UTLaw.MetaVarMVPatterns (UTLaw.MVPatterns name) ->
        case value of
          UT.CVPatterns constructors -> do
            tConstructors <- mapM transform constructors
            return $ Just (name, T.SPatterns tConstructors)
          _ -> throwError "not a list of constructors."
      UTLaw.MetaVarMVCaseStms (UTLaw.MVCaseStms name) ->
        case value of
          UT.CVCaseStms caseStms -> do
            tCaseStms <- mapM transform caseStms
            let dummyTerm = T.TRedWeight 1 $ T.RCase (T.TNum 1) tCaseStms
            checkArgumentTerm dummyTerm
            assert (numHoles dummyTerm == 0) "should not be a context"
            return $ Just (name, T.SCaseStms tCaseStms)
          _ -> throwError "Not a list of case statements"
      UTLaw.MetaVarMVConstructorName (UTLaw.MVConstructorName name) ->
        case value of
          UT.CVConstructorName (UT.ConstructorName name) -> do
            constructors <- gets constructors
            case Map.lookup name constructors of
              Just _ -> return $ Just (name, T.SConstructorName name)
              Nothing -> throwError "Constructor not declared."
          _ -> throwError "Not a constructor name."
    where
      logCheckArg name = Log.logInfoN . pack $ "Checking argument "++name

checkArgumentTerm :: HasCallStack => T.Term -> StCheckM ()
checkArgumentTerm term = do
  checkBoundVariablesDistinct term
  declaredFree <- gets freeVarVars
  let boundVars = getBoundVariables term
  assert (declaredFree `Set.disjoint` boundVars) $ "argument cannot "
    ++"bind declared free variables."

checkAllSubstitutionsProvided ::
  (MonadError String m, Log.MonadLogger m, HasCallStack) =>
  Law.Law -> T.Substitutions -> m ()
checkAllSubstitutionsProvided (Law.DLaw _name term1 _impRel term2 _sideCond)
                              substMap = do
  let metaVars1 = getAllMetaVars term1
      metaVars2 = getAllMetaVars term2
      substitutedVars = Map.keysSet substMap
  assert ((metaVars1 `Set.union` metaVars2) == substitutedVars)
    "Currently, you need to specify all substitutions."

isReductionContext :: T.Term -> Bool
isReductionContext outerTerm =
  numHoles outerTerm == 1 && rightStructure
 where
   rightStructure = case outerTerm of
     T.TNonTerminating -> False
     T.TVar _ -> False
     T.TNum _ -> False
     T.TConstructor _ _ -> False
     T.TLam _ _ -> False
     T.THole -> False
     T.TLet _ _ -> False
     T.TDummyBinds _ _ -> False
     T.TStackSpikes _ _ -> False
     T.THeapSpikes _ _ -> False
     T.TRedWeight _ red -> case red of
       T.RApp T.THole _ -> True
       T.RCase T.THole _ -> True
       T.RPlusWeight T.THole _ _ -> True
       T.RAddConst _ T.THole -> True
       T.RIsZero T.THole -> True
       T.RSeq T.THole _ -> True
       _ -> False

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module LawTypeChecker (typecheckLaws) where

import qualified AbsSieLaws as UT
import qualified TypedLawAST as T
import CheckMonad (CheckM, runCheckM, assert, assertInternal)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Common as Com

typecheckLaws :: UT.LawList -> Either [String] T.LawMap
typecheckLaws lawList = runCheckM typecheckLaws'
  where
    typecheckLaws' = do
      let UT.DLawList innerLawList = lawList
      tLawList <- mapM transform innerLawList
      mapM checkLaw tLawList
      let entryList = map toEntry tLawList
          lawMap = Map.fromList entryList
      return lawMap

    toEntry law = let T.DLaw name _ _ _ _ = law
                  in (name, law)

class Transformable a where
  type TypedVersion a
  transform :: a -> CheckM (TypedVersion a)

instance Transformable UT.Law where
  type TypedVersion UT.Law = T.Law
  transform (UT.DLaw name term1 imp term2 side) = do
    let UT.CommandName strName = name
    tTerm1 <- transform term1
    tTerm2 <- transform term2
    (tImpRel, switch) <- transformImpRel imp
    tSide <- transform side
    if switch
      then return $ T.DLaw strName tTerm2 tImpRel tTerm1 tSide
      else return $ T.DLaw strName tTerm1 tImpRel tTerm2 tSide

instance Transformable UT.Term where
  type TypedVersion UT.Term = T.Term
  transform = \case
    UT.TValueMetaVar mvValue -> let (UT.MVValue str) = mvValue
                                in return $ T.TValueMetaVar str
    UT.TGeneralMetaVar mvTerm -> noSupport "TGeneralMetaVar"
    UT.TVar var -> noSupport "TVar"
    UT.TAppCtx mvContext term -> do
      let (UT.MVContext str) = mvContext
      tTerm <- transform term
      return $ T.TAppCtx str tTerm
    UT.TAppValCtx mVValueContext term -> noSupport "TAppValCtx"
    UT.TNonTerminating -> noSupport "TNonTerminating"
    UT.TNum integer -> noSupport "TNum"
    UT.TIndVar var indExpr -> noSupport "TIndVar"
    UT.TConstructor constructor -> noSupport "TConstructor"
    UT.TStackSpike term -> noSupport "TStackSpike"
    UT.TStackSpikes stackWeight term -> noSupport "TStackSpikes"
    UT.THeapSpike term -> noSupport "THeapSpike"
    UT.THeapSpikes heapWeight term -> noSupport "THeapSpikes"
    UT.TDummyBinds varSet term -> do
      tTerm <- transform term
      tVarSet <- transform varSet
      return $ T.TDummyBinds tVarSet tTerm
    UT.TRedMetaVar mvReduction term -> noSupport "TRedMetaVar"
    UT.TRedMetaVarW redWeight mvReduction term -> noSupport "TRedMetaVarW"
    UT.TSubstitution term v1 v2 -> noSupport "TSubstitution"
    UT.TRApp term var -> noSupport "TRApp"
    UT.TRAppW rw term var -> noSupport "TRAppW"
    UT.TRPlus term1 term2 -> noSupport "TRPlus"
    UT.TRPlusW1 rw term1 term2 -> noSupport "TRPlusW1"
    UT.TRPlusW2 term1 rw term2 -> noSupport "TRPlusW2"
    UT.TRPlusWW rw1 term1 rw2 term2 -> noSupport "TRPlusWW"
    UT.TLam var term -> noSupport "TLam"
    UT.TLet lbs term -> do
      tLbs <- transform lbs
      tTerm <- transform term
      return $ T.TLet tLbs tTerm
    UT.TRCase mRw term caseStms -> noSupport "TRCase"
    UT.TRAddConst mRw integer term -> noSupport "TRAddConst"
    UT.TRIsZero mRw term -> noSupport "TRIsZero"
    UT.TRSeq mRw term1 term2 -> noSupport "TRSeq"

-- | Given an improvement relation, returns the corresponding left-to right
-- improvement relation and a boolean being True if the arguments should be
-- flipped.
transformImpRel :: UT.ImpRel -> CheckM (Com.ImpRel, Bool)
transformImpRel UT.DefinedEqual = return (Com.DefinedEqual, False)
transformImpRel UT.StrongImprovementLR = return (Com.StrongImprovementLR, False)
transformImpRel UT.WeakImprovementLR = return (Com.WeakImprovementLR, False)
transformImpRel UT.StrongImprovementRL = return (Com.StrongImprovementLR, True)
transformImpRel UT.WeakImprovementRL = return (Com.WeakImprovementLR, True)
transformImpRel UT.StrongCostEquiv = return (Com.StrongCostEquiv, False)
transformImpRel UT.WeakCostEquiv = return (Com.StrongCostEquiv, False)
transformImpRel UT.Reduction = noSupport "Reduction"

instance Transformable UT.LetBindings where
  type TypedVersion UT.LetBindings = T.LetBindings
  transform = \case
    UT.LBSOnlyMeta metaBinds -> noSupport "LBSOnlyMeta"
    UT.LBSBoth (metaBinds:[]) letBinds -> case metaBinds of
      UT.MBSMetaVar mvBinds -> do
        let (UT.MVLetBindings str) = mvBinds
        tLetBinds <- mapM transformLB letBinds
        return $ T.LBSBoth (T.MBSMetaVar str) tLetBinds
        where
          transformLB (UT.DLetBinding var bindSym term) = do
            (tsw,thw) <- case bindSym of
              UT.BSWeights sw hw -> do
                let (UT.DStackWeight swIexpr) = sw
                let (UT.DHeapWeight hwIexpr) = hw
                tsw' <- transform swIexpr
                thw' <- transform hwIexpr
                return (tsw', thw')
              UT.BSNoWeight -> return (T.IENum 1,T.IENum 1)
            let varStr = getVarName var
            tTerm <- transform term
            return $ T.DLetBinding varStr tsw thw tTerm
      UT.MBSSubstitution mvBinds var1 var2 -> noSupport "MBSSubstitution"
    UT.LBSBoth metaBinds letBinds -> noSupport $ "multiple bind-sets in meta-"
      ++"variables (LBSBoth, general case)"

instance Transformable UT.IntExpr where
  type TypedVersion UT.IntExpr = T.IntExpr
  transform (UT.IEVar (UT.DIntegerVar (UT.MVIntegerVar varStr))) =
    return $ T.IEVar varStr
  transform (UT.IENum integer) = return $ T.IENum integer
  transform (UT.IEPlus intExpr1 intExpr2) = noSupport "IEPlus"
  transform (UT.IEMinus intExpr1 intExpr2) = noSupport "IEMinus"

instance Transformable UT.VarSet where
  type TypedVersion UT.VarSet = T.VarSet
  transform (UT.VSMetaVar mv) = noSupport "VSMetaVar"
  transform (UT.VSConcrete varList) = let strList = map getVarName varList
                                          strSet = Set.fromList strList
                                      in return $ T.VSConcrete strSet
  transform (UT.VSFreeVars varContainer) = noSupport "VSFreeVars"
  transform (UT.VSDomain mVLetBindings) = noSupport "VSDomain"

instance Transformable UT.SideCond where
  type TypedVersion UT.SideCond = T.SideCond
  transform (UT.NoSideCond) = return T.NoSideCond
  transform (UT.WithSideCond boolTerm) = noSupport "side conditions"

getVarName :: UT.Var -> String
getVarName (UT.DVar (UT.MVVar varStr)) = varStr

noSupport :: String -> CheckM a
noSupport spec = throwError $ spec ++ "not supported yet"

------------------------Checking--------------------

-- | Checks if laws are supported, but does not check if they are sound wrt
-- space improvement.
checkLaw :: T.Law -> CheckM ()
checkLaw = contextsValidInLaw

-- | Checks that contexts are only used in the way that is currently supported.
-- See error text for explanation.
contextsValidInLaw :: T.Law -> CheckM ()
contextsValidInLaw (T.DLaw _name term1 _imprel term2 _sidecond) =
  assert (contextsValid term1 && contextsValid term2) $ "Contexts should only "
    ++"be used in a way that is currently supported.\n"
    ++"> If a context is mentioned more than once, the context may not\n"
    ++"  capture variables.\n"
    ++"> If a context is inside another context, the term inside the inner\n"
    ++"  context may not capture variables. For example, the term C[D[M]] is\n"
    ++"  not allowed, but the term let x = M in C[D[x]] is allowed.\n"
    ++"> A context may not be repeated inside itself, like \n"
    ++"  let x = M in C[C[x]] for example"
    ++"The way SIE checks if a term captures variables is that it checks if the"
    ++"inner term may have free variables. Since all variable names are unique,"
    ++"variables, constructors et cetera do not contain free variables, but" ++"general term meta-variables (M, V, N, C[N], et cetera) may do so."

contextsValid :: T.Term -> Bool
contextsValid term =
  let innerPotentialFail = getTermsInsideRepeatedCtxs term
      innerNotCapturing = all (\t -> not (isTermWithFreeVars t))
                              innerPotentialFail
      contextNotRepeatedInside = not (contextRepeatedInside term)
  in innerNotCapturing && contextNotRepeatedInside

-- | If the term mentions a context twice or inside another context
-- (as described in checkLaw), this function returns a list of the terms inside
-- the repeated contexts.
getTermsInsideRepeatedCtxs :: T.Term -> [T.Term]
getTermsInsideRepeatedCtxs term = getInRepeated ++ getInInner
  where
    getInRepeated = evalState (getInRepeated' term) Map.empty

    -- getInRepeated'  term    (Currently mentioned contexts)
    getInRepeated' :: T.Term -> State (Map.Map String T.Term) [T.Term]
    getInRepeated' (T.TValueMetaVar _) = return []
    getInRepeated' (T.TAppCtx ctxVar term) = do
      mentionedCtxs <- get
      case Map.lookup ctxVar mentionedCtxs of
        Just oldTerm -> return [term, oldTerm]
        Nothing -> do
          let mentionedCtxs' = Map.insert ctxVar term mentionedCtxs
          put mentionedCtxs'
          return [] -- We are only looking at the base level here.
    getInRepeated' (T.TLet letBinds term) = do
      letBindRepeats <- mapM getInRepeated' $ getLetTerms letBinds
      let letBindRepeats' = concat letBindRepeats
      inRepeats <- getInRepeated' term
      return $ letBindRepeats' ++ inRepeats
    getInRepeated' (T.TDummyBinds (T.VSConcrete _vs) term) = getInRepeated' term

    getInInner = getInInner' False term
    --         IsInsideCtx  term
    getInInner' :: Bool -> T.Term -> [T.Term]
    getInInner' _ (T.TValueMetaVar _) = []
    getInInner' False (T.TAppCtx _ term) = getInInner' True term
    getInInner' True (T.TAppCtx _ term) = [term]
    getInInner' isInsideCtx (T.TLet lets term) =
      let letInners = concat $ map (getInInner' isInsideCtx) $ getLetTerms lets
          inInners = getInInner' isInsideCtx term
      in letInners ++ inInners
    getInInner' isInsideCtx (T.TDummyBinds (T.VSConcrete _vs) term) =
      getInInner' isInsideCtx term

getLetTerms :: T.LetBindings -> [T.Term]
getLetTerms (T.LBSBoth _metabindset letBindings) = map getLetTerm letBindings
  where
    getLetTerm (T.DLetBinding _var _sw _hw term) = term

-- | returns whether the term contains a context inside itself, like
-- let x = M in C[C[x]] for example
contextRepeatedInside :: T.Term -> Bool
contextRepeatedInside = \case
  T.TValueMetaVar _ -> False
  T.TAppCtx ctxMV term -> let ctxVars = getCtxVars term
                              repeatedHere = Set.member ctxMV ctxVars
                              repeatedInside = contextRepeatedInside term
                          in repeatedHere || repeatedInside
  T.TLet lbs term ->
    let repeatedLet = any contextRepeatedInside $ getLetTerms lbs
        repeatedIn = contextRepeatedInside term
    in repeatedLet || repeatedIn
  T.TDummyBinds (T.VSConcrete varSet) term -> contextRepeatedInside term
  where
    getCtxVars :: T.Term -> Set.Set String
    getCtxVars (T.TValueMetaVar _) = Set.empty
    getCtxVars (T.TAppCtx ctxVar term) = Set.union (Set.singleton ctxVar)
                                                   (getCtxVars term)
    getCtxVars (T.TLet lbs term) = Set.union (letCtxslbs lbs) (getCtxVars term)
      where
        letCtxslbs (T.LBSBoth _meta concreteLbs) =
          Set.unions $ map getCtxLB concreteLbs
        getCtxLB (T.DLetBinding _var _sw _hw lbTerm) = getCtxVars lbTerm
    getCtxVars (T.TDummyBinds (T.VSConcrete _vs) term) = getCtxVars term

isTermWithFreeVars :: T.Term -> Bool
isTermWithFreeVars = \case
  T.TValueMetaVar str -> True -- V may contain FV
  T.TAppCtx str term -> True -- C may contain FV
  T.TLet letBindings term -> isTermWithFreeVars term || lbsIsWithFV letBindings
    where
      lbsIsWithFV (T.LBSBoth _ _) = True -- in "let G {} in N", G may conain FV
  T.TDummyBinds (T.VSConcrete _varSet) term -> isTermWithFreeVars term

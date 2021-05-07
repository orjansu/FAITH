{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module LawTypeChecker (typecheckLaws) where

import qualified AbsSieLaws as UT
import qualified TypedLawAST as T
import qualified Control.Monad.Logger as Log
import Data.Text (pack)
import CheckMonad (CheckM, runCheckM, assert, assertInternal, noSupport)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import Control.Monad.Except (throwError, MonadError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Common as Com
import LanguageLogic (trueName, falseName)

typecheckLaws :: UT.LawList -> Either [String] T.LawMap
typecheckLaws lawList = runCheckM typecheckLaws'
  where
    typecheckLaws' = do
      let UT.DLawList innerLawList = lawList
      tLawList <- mapM transform innerLawList
      mapM checkLaw tLawList
      let entryList = map toEntry tLawList
          -- TODO check that all law names are distinct
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
    UT.TGeneralMetaVar (UT.MVTerm mvTerm) -> return $ T.TGeneralMetaVar mvTerm
    UT.TMVTerms (UT.MVTerms str) -> return $ T.TMVTerms str
    UT.TVar var -> let varStr = getVarName var
                   in return $ T.TVar varStr
    UT.TAppCtx mvContext term -> do
      let (UT.MVContext str) = mvContext
      tTerm <- transform term
      return $ T.TAppCtx str tTerm
    UT.TAppValCtx (UT.MVValueContext mvValCtx) term -> do
      tTerm <- transform term
      return $ T.TAppValCtx mvValCtx tTerm
    UT.TNonTerminating -> return T.TNonTerminating
    UT.TNum integer -> return $ T.TNum integer
    UT.TIndVar var indExpr -> noSupport "TIndVar"
    UT.TConstructor constructor -> do
      tConstructor <- transform constructor
      return $ T.TConstructor tConstructor
    UT.TStackSpike term -> do
      tTerm <- transform term
      return $ T.TStackSpikes (T.IENum 1) tTerm
    UT.TStackSpikes (UT.DStackWeight stackWeight) term -> do
      tTerm <- transform term
      tSw <- transform stackWeight
      return $ T.TStackSpikes tSw tTerm
    UT.THeapSpike term -> do
      tTerm <- transform term
      return $ T.THeapSpikes (T.IENum 1) tTerm
    UT.THeapSpikes (UT.DHeapWeight hw) term -> do
      tHw <- transform hw
      tTerm <- transform term
      return $ T.THeapSpikes tHw tTerm
    UT.TDummyBinds varSet term -> do
      tTerm <- transform term
      tVarSet <- transform varSet
      return $ T.TDummyBinds tVarSet tTerm
    UT.TRedMetaVar mvReduction term -> do
      tTerm <- transform term
      let (UT.MVReduction str) = mvReduction
      return $ T.TRedWeight (T.IENum 1) $ T.RMetaVar str tTerm
    UT.TRedMetaVarW redWeight mvReduction term -> do
      let (UT.DRedWeight (UT.DStackWeight rw)) = redWeight
      tRW <- transform rw
      let (UT.MVReduction str) = mvReduction
      tTerm <- transform term
      return $ T.TRedWeight tRW $ T.RMetaVar str tTerm
    UT.TSubstitution term v1 v2 -> do
      tTerm <- transform term
      let (UT.DVar (UT.MVVar v1str)) = v1
          (UT.DVar (UT.MVVar v2str)) = v2
      return $ T.TSubstitution tTerm v1str v2str
    UT.TRApp term (UT.DVar (UT.MVVar varName)) -> do
      tTerm <- transform term
      return $ T.TRedWeight (T.IENum 1) $ T.RApp tTerm varName
    UT.TRAppW (UT.DRedWeight (UT.DStackWeight rw)) term var -> do
      trw <- transform rw
      tTerm <- transform term
      let (UT.DVar (UT.MVVar vName)) = var
      return $ T.TRedWeight trw $ T.RApp tTerm vName
    UT.TRAppNoW term (UT.DVar (UT.MVVar varName)) -> do
      tTerm <- transform term
      return $ T.TRedWeight (T.IENum 0) $ T.RApp tTerm varName
    UT.TRPlus term1 term2 -> transformPlus Nothing term1 Nothing term2
    UT.TRPlusW1 rw term1 term2 ->
      transformPlus (Just rw) term1 Nothing term2
    UT.TRPlusW2 term1 rw term2 ->
      transformPlus Nothing term1 (Just rw) term2
    UT.TRPlusWW rw1 term1 rw2 term2 ->
      transformPlus (Just rw1) term1 (Just rw2) term2
    UT.TLam (UT.DVar (UT.MVVar var)) term -> do
      tTerm <- transform term
      return $ T.TLam var tTerm
    UT.TLet lbs term -> do
      tLbs <- transform lbs
      tTerm <- transform term
      return $ T.TLet tLbs tTerm
    UT.TRCase mRw term caseStms -> do
      rw <- transform mRw
      tTerm <- transform term
      tCaseStms <- mapM transCase caseStms
      return $ T.TRedWeight rw $ T.RCase tTerm tCaseStms
      -- Correctness in terms of what case statement patterns that are allowed
      -- are checked in checkLaw.
      where
        transCase (UT.CSAlts (UT.MVCaseStms str)) = return $ T.CSAlts str
        transCase (UT.CSPatterns (UT.MVPatterns str) term) = do
          tTerm <- transform term
          return $ T.CSPatterns str tTerm
        transCase (UT.CSConcrete constr term) = do
          tConstr <- transform constr
          tTerm <- transform term
          return $ T.CSConcrete tConstr tTerm

    UT.TRAddConst mRw intExpr term -> do
      tRw <- transform mRw
      tIE <- transform intExpr
      tTerm <- transform term
      return $ T.TRedWeight tRw $ T.RAddConst tIE tTerm
    UT.TRIsZero mRw term -> do
      tRW <- transform mRw
      tTerm <- transform term
      return $ T.TRedWeight tRW $ T.RIsZero tTerm
    UT.TRSeq mRw term1 term2 -> do
      tRW <- transform mRw
      tTerm1 <- transform term1
      tTerm2 <- transform term2
      return $ T.TRedWeight tRW $ T.RSeq tTerm1 tTerm2

transformPlus :: Maybe UT.RedWeight -> UT.Term -> Maybe UT.RedWeight -> UT.Term
                 -> CheckM T.Term
transformPlus mrw1 t1 mrw2 t2 = do
  tRW1 <- transMrw mrw1
  tTerm1 <- transform t1
  tRW2 <- transMrw mrw2
  tTerm2 <- transform t2
  return $ T.TRedWeight tRW1 $ T.RPlusW tTerm1 tRW2 tTerm2
  where
    transMrw Nothing = return $ T.IENum 1
    transMrw (Just (UT.DRedWeight (UT.DStackWeight expr))) = transform expr

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

instance Transformable UT.LetBindings where
  type TypedVersion UT.LetBindings = T.LetBindings
  transform = \case
    UT.LBSOnlyMeta metaBinds -> do
      tMetaBinds <- mapM transform metaBinds
      return $ T.LBSBoth tMetaBinds []
    UT.LBSBoth metaBinds letBinds -> do
      tMetaBinds <- mapM transform metaBinds
      tLetBinds <- mapM transformLB letBinds
      return $ T.LBSBoth tMetaBinds tLetBinds
      where
        transformLB (UT.LBConcrete var bindSym term) = do
          (tsw,thw) <- transform bindSym
          let varStr = getVarName var
          tTerm <- transform term
          return $ T.LBConcrete varStr tsw thw tTerm
        transformLB (UT.LBVectorized vect1 bindSym vect2) = do
          (tsw, thw) <- transform bindSym
          let (UT.MVVarVect vectStr1) = vect1
              (UT.MVVarVect vectStr2) = vect2
          return $ T.LBVectorized vectStr1 tsw thw vectStr2

instance Transformable UT.BindSymbol where
  type TypedVersion UT.BindSymbol = (T.IntExpr, T.IntExpr)
  transform (UT.BSWeights sw hw) = do
    let (UT.DStackWeight swIexpr) = sw
    let (UT.DHeapWeight hwIexpr) = hw
    tsw' <- transform swIexpr
    thw' <- transform hwIexpr
    return (tsw', thw')
  transform UT.BSNoWeight = return (T.IENum 1,T.IENum 1)

instance Transformable UT.MetaBindSet where
  type TypedVersion UT.MetaBindSet = T.MetaBindSet
  transform (UT.MBSMetaVar (UT.MVLetBindings mv)) = return $ T.MBSMetaVar mv
  transform (UT.MBSSubstitution mvLet var1 var2) =
    let (UT.MVLetBindings mvLetName) = mvLet
        (UT.DVar (UT.MVVar var1Name)) = var1
        (UT.DVar (UT.MVVar var2Name)) = var2
    in return $ T.MBSSubstitution mvLetName var1Name var2Name


instance Transformable UT.IntExpr where
  type TypedVersion UT.IntExpr = T.IntExpr
  transform (UT.IEVar (UT.DIntegerVar (UT.MVIntegerVar varStr))) =
    return $ T.IEVar varStr
  transform (UT.IENum integer) = return $ T.IENum integer
  transform (UT.IESizeBind (UT.MVLetBindings str)) =
    return $ T.IESizeBind str
  transform (UT.IEPlus intExpr1 intExpr2) = do
    tIntExpr1 <- transform intExpr1
    tIntExpr2 <- transform intExpr2
    return $ T.IEPlus tIntExpr1 tIntExpr2
  transform (UT.IEMinus intExpr1 intExpr2) = do
    tIntExpr1 <- transform intExpr1
    tIntExpr2 <- transform intExpr2
    return $ T.IEMinus tIntExpr1 tIntExpr2

instance Transformable UT.MaybeRedWeight where
  type TypedVersion UT.MaybeRedWeight = T.IntExpr
  transform (UT.WithRedWeight (UT.DRedWeight (UT.DStackWeight expr))) =
    transform expr
  transform UT.NoRedWeight = return $ T.IENum 1

instance Transformable UT.VarSet where
  type TypedVersion UT.VarSet = T.VarSet
  transform (UT.VSMetaVar (UT.MVVarSet mv)) = return $ T.VSMetaVar mv
  transform (UT.VSConcrete varList) = let strList = map getVarName varList
                                          strSet = Set.fromList strList
                                      in return $ T.VSConcrete strSet
  transform (UT.VSFreeVars varContainer) = do
    tVarContainer <- transform varContainer
    return $ T.VSFreeVars tVarContainer
  transform (UT.VSDomain (UT.MVLetBindings str)) =
    return $ T.VSDomain str
  transform (UT.VSUnion setTerm1 setTerm2) = do
    tSetTerm1 <- transform setTerm1
    tSetTerm2 <- transform setTerm2
    return $ T.VSUnion tSetTerm1 tSetTerm2
  transform (UT.VSDifference setTerm1 setTerm2) = do
    tSetTerm1 <- transform setTerm1
    tSetTerm2 <- transform setTerm2
    return $ T.VSDifference tSetTerm1 tSetTerm2
  transform (UT.VSVectMeta (UT.MVVarVect str)) =
    return $ T.VSVectMeta str

instance Transformable UT.VarContainer where
  type TypedVersion UT.VarContainer = T.VarContainer
  transform (UT.VCTerm term) = do
    tTerm <- transform term
    return $ T.VCTerm tTerm
  transform (UT.VCMetaVarContext (UT.MVContext str)) =
    return $ T.VCMetaVarContext str
  transform (UT.VCMetaVarRed (UT.MVReduction str)) =
    return $ T.VCMetaVarRed str
  transform (UT.VCValueContext (UT.MVValueContext str)) =
    return $ T.VCValueContext str

instance Transformable UT.SideCond where
  type TypedVersion UT.SideCond = T.SideCond
  transform (UT.NoSideCond) = return T.NoSideCond
  transform (UT.WithSideCond boolTerm) = do
    tBt <- transform boolTerm
    return $ T.WithSideCond tBt


instance Transformable UT.BoolTerm where
  type TypedVersion UT.BoolTerm = T.BoolTerm
  transform (UT.BTSizeEq mVLetBindings1 mVLetBindings2) =
    let (UT.MVLetBindings str1) = mVLetBindings1
        (UT.MVLetBindings str2) = mVLetBindings2
    in return $ T.BTSizeEq str1 str2
  transform (UT.BTSetEq setTerm1 setTerm2) = do
    tsetTerm1 <- transform setTerm1
    tSetTerm2 <- transform setTerm2
    return $ T.BTSetEq tsetTerm1 tSetTerm2
  transform (UT.BTSubsetOf setTerm1 setTerm2) = do
    tsetTerm1 <- transform setTerm1
    tSetTerm2 <- transform setTerm2
    return $ T.BTSubsetOf tsetTerm1 tSetTerm2
  transform (UT.BTIn var setTerm) = do
    let tvar = getVarName var
    tSetTerm <- transform setTerm
    return $ T.BTIn tvar tSetTerm
  transform (UT.BTNot subBoolTerm) = do
    tSubBoolTerm <- transform subBoolTerm
    return $ T.BTNot tSubBoolTerm
  transform (UT.BTLE ie1 ie2) = do
    tIE1 <- transform ie1
    tIE2 <- transform ie2
    return $ T.BTLE tIE1 tIE2
  transform (UT.BTGE ie1 ie2) = do
    tIE1 <- transform ie1
    tIE2 <- transform ie2
    return $ T.BTGE tIE1 tIE2
  transform (UT.BTGT ie1 ie2) = do
    tIE1 <- transform ie1
    tIE2 <- transform ie2
    return $ T.BTGT tIE1 tIE2
  transform (UT.BTIsFresh var) =
    let varName = getVarName var
    in return $ T.BTIsFresh varName
  transform (UT.BTAreFresh vars) =
    let (UT.MVVarVect str) = vars
    in return $ T.BTAreFresh str
  transform (UT.BTReducesTo reduction value term) = do
    let UT.MVReduction rStr = reduction
        UT.MVValue vStr = value
    tTerm <- transform term
    return $ T.BTReducesTo rStr vStr tTerm
  transform (UT.BTAnd bt1 bt2) = do
    tBT1 <- transform bt1
    tBT2 <- transform bt2
    return $ T.BTAnd tBT1 tBT2

instance Transformable UT.Constructor where
  type TypedVersion UT.Constructor = T.Constructor
  transform (UT.CGeneral (UT.MVConstructorName name) (UT.MVVarVect args)) =
    return $ T.CGeneral name args
  transform UT.CTrue = return $ T.CGeneral trueName []
  transform UT.CFalse = return $ T.CGeneral falseName []

getVarName :: UT.Var -> String
getVarName (UT.DVar (UT.MVVar varStr)) = varStr

------------------------Checking--------------------

-- | Checks if laws are supported, but does not check if they are sound wrt
-- space improvement.
--
-- TODO: Check that
-- -N_i is only used inside Case statements
-- -letbinding-metavariables are not copied
-- -Metavariables in binding positions are not copied
-- -Case statements are either
--   {alts, [Concrete]}
--   {pat_i -> C[N_i]} or {pat_i -> M} - NOTE that C[N_i] may not contain
--      multiple vectorized expressions (i.e. N_i and N_j), so no nesting
--      of vectorized case statements.
--   {[Concrete]}
--   (The c_i ys_i -> N_i is just for reduction, and I think that I will
--   implement reduction manually)
-- NOTE: new checks:
-- - not (... isfresh ...) and not (... areFresh ...) are not supported.
-- - not (... ReducesTo ...) is not supported.
-- - the N of R[V] ~~> N may not contain indexed expressions.
checkLaw :: T.Law -> CheckM ()
checkLaw (T.DLaw _name term1 _imprel term2 _sidecond) = do
  mapM checkTerm [term1, term2]
  return ()
  where
    checkTerm t = do
      checkLetBindingsNotCopied t
      checkMetaBindVarsNotCopied t
      checkCaseStatements t

checkLetBindingsNotCopied :: T.Term -> CheckM ()
checkLetBindingsNotCopied _ = do
  Log.logInfoN . pack $ "Skipping check checkLetBindingsNotCopied for now."

checkMetaBindVarsNotCopied :: T.Term -> CheckM ()
checkMetaBindVarsNotCopied _ =
  Log.logInfoN . pack $ "Skipping check checkMetaBindVarsNotCopied for now."

checkCaseStatements :: T.Term -> CheckM ()
checkCaseStatements _ =
  Log.logInfoN . pack $ "Skipping check checkCaseStatements for now."

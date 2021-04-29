{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module LawTypeChecker (typecheckLaws) where

import qualified AbsSieLaws as UT
import qualified TypedLawAST as T
import CheckMonad (CheckM, runCheckM, assert, assertInternal, noSupport)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import Control.Monad.Except (throwError, MonadError)
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
    UT.TGeneralMetaVar (UT.MVTerm mvTerm) -> return $ T.TGeneralMetaVar mvTerm
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
    UT.TConstructor constructor -> case constructor of
        UT.CGeneral (UT.MVConstructorName name) (UT.MVVarVect args) ->
          return $ T.TConstructor $ T.CGeneral name args
        UT.CTrue -> return $ T.TConstructor T.CTrue
        UT.CFalse -> return $ T.TConstructor T.CFalse
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
    UT.TRCase mRw term caseStms -> noSupport "TRCase"
      -- To do this, you must include the MVTerms N_i, and you must check that
      -- N_i is only used in terms inside case statements.
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
transformImpRel UT.Reduction = noSupport "Reduction"

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
          return $ (varStr, tsw, thw, tTerm)

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
  transform (UT.WithSideCond boolTerm) = noSupport "side conditions"

getVarName :: UT.Var -> String
getVarName (UT.DVar (UT.MVVar varStr)) = varStr

------------------------Checking--------------------

-- | Checks if laws are supported, but does not check if they are sound wrt
-- space improvement.
--
-- TODO: Check that N_i is only used inside Case statements
checkLaw :: T.Law -> CheckM ()
checkLaw _ = return ()

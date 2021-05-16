{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module ShowLaw (showLaw) where

import qualified Data.Set as Set

import PrintSieLaws ( printTree, Print )

import qualified TypedLawAST as T
import qualified AbsSieLaws as UT
import OtherUtils (filterNoise)
import Common (falseName, trueName)

showLaw :: (Convertible a, Print (UntypedVersion a), Show a) => a -> String
showLaw = filterNoise . printTree . toUntyped

class Convertible a where
  type UntypedVersion a
  toUntyped :: a -> UntypedVersion a

instance Convertible T.Term where
  type UntypedVersion T.Term = UT.Term
  toUntyped (T.TGeneralMetaVar mvName) = UT.TGeneralMetaVar $ UT.MVTerm mvName
  toUntyped (T.TMVTerms mvName) = UT.TMVTerms $ UT.MVTerms mvName
  toUntyped (T.TAppValCtx mvName term) =
    UT.TAppValCtx (UT.MVValueContext mvName) (toUntyped term)
  toUntyped (T.TNonTerminating) = UT.TNonTerminating
  toUntyped (T.TNum integer) = UT.TNum integer
  toUntyped (T.TConstructor constructor) =
    UT.TConstructor (toUntyped constructor)
  toUntyped (T.TStackSpikes intExpr term) =
    UT.TStackSpikes (UT.DStackWeight (toUntyped intExpr)) (toUntyped term)
  toUntyped (T.THeapSpikes intExpr term) =
    UT.THeapSpikes (UT.DHeapWeight (toUntyped intExpr)) (toUntyped term)
  toUntyped (T.TSubstitution term mvName1 mvName2) =
    UT.TSubstitution (toUntyped term)
                     (UT.DVar (UT.MVVar mvName1))
                     (UT.DVar (UT.MVVar mvName2))
  toUntyped (T.TLam mvName term) =
    UT.TLam (UT.DVar (UT.MVVar mvName)) (toUntyped term)
  toUntyped (T.TRedWeight intExpr reduction) =
    let utRW = UT.DRedWeight (UT.DStackWeight (toUntyped intExpr))
        hasWeight = intExpr == (T.IENum 1)
        mRW = if hasWeight
                then UT.WithRedWeight utRW
                else UT.NoRedWeight
    in case reduction of
      T.RMetaVar string term -> if hasWeight
        then UT.TRedMetaVarW utRW (UT.MVReduction string) (toUntyped term)
        else UT.TRedMetaVar (UT.MVReduction string) (toUntyped term)
      T.RApp term string ->
        let var = (UT.DVar (UT.MVVar string))
            utTerm = toUntyped term
        in case intExpr of
             (T.IENum 1) -> UT.TRApp utTerm var
             (T.IENum 0) -> UT.TRAppNoW utTerm var
             _ -> UT.TRAppW utRW utTerm var
      T.RPlusW term1 intExpr2 term2 ->
        let utTerm1 = toUntyped term1
            utTerm2 = toUntyped term2
            utRW2 = UT.DRedWeight (UT.DStackWeight (toUntyped intExpr2))
        in case (intExpr, intExpr2) of
          (T.IENum 1, T.IENum 1) -> UT.TRPlus utTerm1 utTerm2
          (T.IENum 1, _) -> UT.TRPlusW1 utRW utTerm1 utTerm2
          (_, T.IENum 1) -> UT.TRPlusW2 utTerm1 utRW2 utTerm2
          (_,_) -> UT.TRPlusWW utRW utTerm1 utRW2 utTerm2
      T.RCase term stms -> UT.TRCase mRW utTerm utStms
        where
          utTerm = toUntyped term
          utStms = map toUTStm stms
          toUTStm stm = case stm of
            T.CSAlts string -> UT.CSAlts (UT.MVCaseStms string)
            T.CSPatterns string term -> UT.CSPatterns (UT.MVPatterns string)
                                                      (toUntyped term)
            T.CSConcrete constructor term ->
              UT.CSConcrete (toUntyped constructor) (toUntyped term)
      T.RAddConst intExpr term ->
        UT.TRAddConst mRW (toUntyped intExpr) (toUntyped term)
      T.RIsZero term -> UT.TRIsZero mRW (toUntyped term)
      T.RSeq term1 term2 -> UT.TRSeq mRW (toUntyped term1) (toUntyped term2)
  toUntyped (T.TValueMetaVar mvName) = UT.TValueMetaVar $ UT.MVValue mvName
  toUntyped (T.TVar mvName) = UT.TVar $ toUntypedVar mvName
  toUntyped (T.TAppCtx mvName term) = UT.TAppCtx (UT.MVContext mvName)
                                                 (toUntyped term)
  toUntyped (T.TLet letBindings term) = UT.TLet (toUntyped letBindings)
                                                (toUntyped term)
  toUntyped (T.TDummyBinds vs term) =
    let utVarSet = toUntyped vs
        utTerm = toUntyped term
    in UT.TDummyBinds utVarSet utTerm

toUntypedVar :: String -> UT.Var
toUntypedVar mvName = UT.DVar $ UT.MVVar mvName

instance Convertible T.LetBindings where
  type UntypedVersion T.LetBindings = UT.LetBindings
  toUntyped (T.LBSBoth tMBS letBindings) =
    let mbs = map toMBS tMBS
        lbs = map toLB letBindings
    in UT.LBSBoth mbs lbs
    where
      toMBS (T.MBSMetaVar mv) = UT.MBSMetaVar (UT.MVLetBindings mv)
      toMBS (T.MBSSubstitution string var1 var2) =
        let utLB = UT.MVLetBindings string
            utVar1 = UT.DVar (UT.MVVar var1)
            utVar2 = UT.DVar (UT.MVVar var2)
        in UT.MBSSubstitution utLB utVar1 utVar2
      toLB (T.LBConcrete var sw hw term) =
        let utVar = toUntypedVar var
            utSw = toUntyped sw
            utHw = toUntyped hw
            utTerm = toUntyped term
            bindSym = toBindSym utSw utHw
        in UT.LBConcrete utVar bindSym utTerm
      toLB (T.LBVectorized varVect1 sw hw varVect2) =
        let utSw = toUntyped sw
            utHw = toUntyped hw
            bindSym = toBindSym utSw utHw
        in UT.LBVectorized (UT.MVVarVect varVect1)
                           bindSym
                           (UT.MVVarVect varVect2)

      toBindSym (UT.IENum 1) (UT.IENum 1) = UT.BSNoWeight
      toBindSym sw hw = UT.BSWeights (UT.DStackWeight sw) (UT.DHeapWeight hw)

instance Convertible T.IntExpr where
  type UntypedVersion T.IntExpr = UT.IntExpr
  toUntyped (T.IEVar str) = UT.IEVar $ UT.DIntegerVar $ UT.MVIntegerVar str
  toUntyped (T.IENum integer) = UT.IENum integer
  toUntyped (T.IESizeBind string) = UT.IESizeBind (UT.MVLetBindings string)
  toUntyped (T.IEPlus intExpr1 intExpr2) =
    UT.IEPlus (toUntyped intExpr1) (toUntyped intExpr2)
  toUntyped (T.IEMinus intExpr1 intExpr2) =
    UT.IEMinus (toUntyped intExpr1) (toUntyped intExpr2)

instance Convertible T.VarSet where
  type UntypedVersion T.VarSet = UT.VarSet
  toUntyped (T.VSConcrete varSet) =
    UT.VSConcrete $ map toUntypedVar $ Set.toList varSet
  toUntyped (T.VSMetaVar string) = UT.VSMetaVar $ UT.MVVarSet string
  toUntyped (T.VSVectMeta string) = UT.VSVectMeta $ UT.MVVarVect string
  toUntyped (T.VSFreeVars varContainer) = UT.VSFreeVars utVC
    where
      utVC = case varContainer of
        T.VCTerm t -> UT.VCTerm (toUntyped t)
        T.VCMetaVarContext str -> UT.VCMetaVarContext $ UT.MVContext str
        T.VCMetaVarRed str -> UT.VCMetaVarRed $ UT.MVReduction str
        T.VCValueContext str -> UT.VCValueContext $ UT.MVValueContext str
  toUntyped (T.VSDomain mvLetBindings) =
    UT.VSDomain (UT.MVLetBindings mvLetBindings)
  toUntyped (T.VSUnion varSet1 varSet2) =
    UT.VSUnion (toUntyped varSet1) (toUntyped varSet2)
  toUntyped (T.VSDifference varSet1 varSet2) =
    UT.VSDifference (toUntyped varSet1) (toUntyped varSet2)

instance Convertible T.Constructor where
  type UntypedVersion T.Constructor = UT.Constructor
  toUntyped (T.CGeneral name args)
    | name == trueName = UT.CTrue
    | name == falseName = UT.CFalse
    | otherwise = UT.CGeneral (UT.MVConstructorName name)
                              (UT.MVVarVect args)

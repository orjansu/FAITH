{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module ShowLaw (showLaw) where

import qualified Data.Set as Set

import PrintSieLaws ( printTree, Print )

import qualified TypedLawAST as T
import qualified AbsSieLaws as UT
import OtherUtils (filterNoise)

showLaw :: (Convertible a, Print (UntypedVersion a)) => a -> String
showLaw = filterNoise . printTree . toUntyped

class Convertible a where
  type UntypedVersion a
  toUntyped :: a -> UntypedVersion a

instance Convertible T.Term where
  type UntypedVersion T.Term = UT.Term
  toUntyped (T.TValueMetaVar mvName) = UT.TValueMetaVar $ UT.MVValue mvName
  toUntyped (T.TVar mvName) = UT.TVar $ toUntypedVar mvName
  toUntyped (T.TAppCtx mvName term) = UT.TAppCtx (UT.MVContext mvName)
                                                 (toUntyped term)
  toUntyped (T.TLet letBindings term) = UT.TLet (toUntyped letBindings)
                                                (toUntyped term)
  toUntyped (T.TDummyBinds (T.VSConcrete varSet) term) =
    let utVarSet = UT.VSConcrete $ map toUntypedVar $ Set.toList varSet
        utTerm = toUntyped term
    in UT.TDummyBinds utVarSet utTerm

toUntypedVar :: String -> UT.Var
toUntypedVar mvName = UT.DVar $ UT.MVVar mvName

instance Convertible T.LetBindings where
  type UntypedVersion T.LetBindings = UT.LetBindings
  toUntyped (T.LBSBoth (T.MBSMetaVar mv) letBindings) =
    let mbs = [UT.MBSMetaVar (UT.MVLetBindings mv)]
        lbs = map toLB letBindings
    in UT.LBSBoth mbs lbs
    where
      toLB (var, sw, hw, term) =
        let utVar = toUntypedVar var
            utSw = toUntyped sw
            utHw = toUntyped hw
            utTerm = toUntyped term
            bindSym = toBindSym utSw utHw
        in UT.DLetBinding utVar bindSym utTerm

      toBindSym (UT.IENum 1) (UT.IENum 1) = UT.BSNoWeight
      toBindSym sw hw = UT.BSWeights (UT.DStackWeight sw) (UT.DHeapWeight hw)

instance Convertible T.IntExpr where
  type UntypedVersion T.IntExpr = UT.IntExpr
  toUntyped (T.IEVar str) = UT.IEVar $ UT.DIntegerVar $ UT.MVIntegerVar str
  toUntyped (T.IENum integer) = UT.IENum integer
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module ShowTypedTerm (showTypedTerm, toUntyped) where

import qualified Data.Set as Set

import PrintSie                 ( printTree, Print )

import qualified MiniTypedAST as T
import qualified AbsSie as UT
import OtherUtils (filterNoise)

showTypedTerm :: (Convertible a, Print (UntypedVersion a)) => a -> String
showTypedTerm = filterNoise . printTree . toUntyped

class Convertible a where
  type UntypedVersion a
  toUntyped :: a -> UntypedVersion a

instance Convertible T.Term where
  type UntypedVersion T.Term = UT.Term
  toUntyped (T.TVar var) =  UT.TVar $ UT.DVar $ UT.Ident var
  toUntyped (T.TNum integer) = UT.TNum integer
  toUntyped (T.TLam var term ) = UT.TLam (UT.DVar (UT.Ident var))
                                         (toUntyped term)
  toUntyped (T.THole) = UT.THole
  toUntyped (T.TLet letBindings term) = UT.TLet (toUntyped letBindings)
                                             (toUntyped term)
  toUntyped (T.TDummyBinds varSet term) =
    let utVarSet = UT.DVarSet $ map toUtVar $ Set.toAscList $ varSet
        utTerm = toUntyped term
    in UT.TDummyBinds utVarSet utTerm
    where
      toUtVar :: String -> UT.Var
      toUtVar = UT.DVar . UT.Ident
  toUntyped (T.TRedWeight 1 red) = case red of
    T.RApp term var -> let utTerm = toUntyped term
                           utVar = toUntypedVar var
                       in UT.TRApp utTerm utVar
    T.RPlusWeight term1 rw term2 ->
      let utTerm1 = toUntyped term1
          utTerm2 = toUntyped term2
      in case rw of
        1 -> UT.TRPlus utTerm1 utTerm2
        _ -> let utWeight = toUntypedRedWeight rw
             in UT.TRPlusW2 utTerm1 utWeight utTerm2
  toUntyped (T.TRedWeight redWeight red) =
    let utRedw = toUntypedRedWeight redWeight
    in case red of
         T.RApp term var -> let utTerm = toUntyped term
                                utVar = toUntypedVar var
                            in UT.TRAppW utRedw utTerm utVar
         T.RPlusWeight term1 rw term2 ->
           let utTerm1 = toUntyped term1
               utTerm2 = toUntyped term2
           in case rw of
             1 -> UT.TRPlusW1 utRedw utTerm1 utTerm2
             _ -> let utWeight2 = toUntypedRedWeight rw
                  in UT.TRPlusWW utRedw utTerm1 utWeight2 utTerm2

instance Convertible T.LetBindings where
  type UntypedVersion T.LetBindings = UT.LetBindings
  toUntyped tLets = UT.LBSSet (map toUTLetBinding tLets)
    where
    toUTLetBinding :: (String, Integer, Integer, T.Term) -> UT.LetBinding
    toUTLetBinding (name, sw, hw, term) =
      let utName = UT.DVar $ UT.Ident name
          utTerm = toUntyped term
          utBindsymbol = case (sw, hw) of
            (1,1) -> UT.BSNoWeight
            (_,_) -> let utSw = UT.StackWeightExpr $ sw
                         utHw = UT.HeapWeightExpr $ hw
                     in UT.BSWeights utSw utHw
      in UT.LBConcrete utName utBindsymbol utTerm

toUntypedVar :: String -> UT.Var
toUntypedVar name = UT.DVar $ UT.Ident name

toUntypedRedWeight :: Integer -> UT.RedWeight
toUntypedRedWeight rw = UT.DRedWeight $ UT.StackWeightExpr $ rw

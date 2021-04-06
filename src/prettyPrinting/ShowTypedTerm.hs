{-# LANGUAGE TypeFamilies #-}

module ShowTypedTerm (showTypedTerm, toUntyped) where

import qualified Data.Set as Set

import PrintSie                 ( printTree )

import qualified MiniTypedAST as T
import qualified AbsSie as UT

showTypedTerm :: T.Term -> String
showTypedTerm = filterNoise . printTree . toUntyped

filterNoise :: String -> String
filterNoise = filter (/='\n')

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
  toUntyped (T.TLet letBindings term) = UT.TLet (convertLBs letBindings)
                                             (toUntyped term)
    where
      convertLBs :: [(String, Integer, Integer, T.Term)] -> UT.LetBindings
      convertLBs tLets = UT.LBSSet (map toUTLetBinding tLets)

      toUTLetBinding :: (String, Integer, Integer, T.Term) -> UT.LetBinding
      toUTLetBinding (name, sw, hw, term) =
        let utName = UT.DVar $ UT.Ident name
            utTerm = toUntyped term
            utBindsymbol = case (sw, hw) of
              (1,1) -> UT.BSNoWeight
              (_,_) -> let utSw = UT.StackWeightExpr $ UT.IENum sw
                           utHw = UT.HeapWeightExpr $ UT.IENum hw
                       in UT.BSWeights utSw utHw
        in UT.LBConcrete utName utBindsymbol utTerm
  toUntyped (T.TDummyBinds varSet term) =
    let utVarSet = UT.DVarSet $ map toUtVar $ Set.toAscList $ varSet
        utTerm = toUntyped term
    in UT.TDummyBinds utVarSet utTerm
    where
      toUtVar :: String -> UT.Var
      toUtVar = UT.DVar . UT.Ident
  toUntyped (T.TRedWeight 1 red) = UT.TRed $ toUntyped red
  toUntyped (T.TRedWeight redWeight red) =
    let utWeight = UT.DRedWeight $ UT.StackWeightExpr $ UT.IENum redWeight
        utRed = toUntyped red
    in UT.TRedWeight utWeight utRed

instance Convertible T.Red where
  type UntypedVersion T.Red = UT.Red
  toUntyped (T.RApp term var) = let utTerm = toUntyped term
                                    utVar = UT.DVar $ UT.Ident var
                                in UT.RApp utTerm utVar
  toUntyped (T.RPlusWeight term1 rw term2) =
    let utTerm1 = toUntyped term1
        utTerm2 = toUntyped term2
    in case rw of
      1 -> UT.RPlus utTerm1 utTerm2
      _ -> let utWeight = UT.DRedWeight $ UT.StackWeightExpr $ UT.IENum rw
           in UT.RPlusWeight utTerm1 utWeight utTerm2

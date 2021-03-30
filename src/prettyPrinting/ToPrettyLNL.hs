{-# LANGUAGE TypeFamilies #-}

module ToPrettyLNL (showLNL) where

import qualified Data.Set as Set

import qualified LocallyNameless as LNL
import qualified AbsLNL as P
import PrintLNL (printTree)

showLNL :: LNL.Term -> String
showLNL = filterNoise . printTree . toPrintable

filterNoise :: String -> String
filterNoise = filter (\c -> c /='\"' && c /= '\n')

class Convertible a where
  type PrintVersion a
  toPrintable :: a -> PrintVersion a

instance Convertible LNL.Term where
  type PrintVersion LNL.Term = P.Term
  toPrintable (LNL.TVar var) = P.TVar (toPrintable var)
  toPrintable (LNL.TNum int) = P.TNum int
  toPrintable (LNL.THole) = P.THole
  toPrintable (LNL.TLam term) = P.TLam (toPrintable term)
  toPrintable (LNL.TLet letBindings term) = P.TLet (convertLbs letBindings)
                                                   (toPrintable term)
    where
      convertLbs = map convertLB
      convertLB (1,1,term) = P.LBNoWeight (toPrintable term)
      convertLB (sw, hw, term) = P.LBWeight sw hw (toPrintable term)
  toPrintable (LNL.TDummyBinds varSet term) = P.TDummyBinds (convertVS varSet)
                                                            (toPrintable term)
    where
      convertVS = (map toPrintable) . Set.toAscList
  toPrintable (LNL.TRedWeight 1 red) = P.TRed (toPrintable red)
  toPrintable (LNL.TRedWeight redWeight red) = P.TRedWeight redWeight
                                                            (toPrintable red)

instance Convertible LNL.Red where
  type PrintVersion LNL.Red = P.Red
  toPrintable (LNL.RApp term var) = P.RApp (toPrintable term) (toPrintable var)
  toPrintable (LNL.RPlusWeight term1 1 term2) =
    P.RPlus (toPrintable term1) (toPrintable term2)
  toPrintable (LNL.RPlusWeight term1 rw term2) =
    P.RPlusWeight (toPrintable term1) rw (toPrintable term2)

instance Convertible LNL.Var where
  type PrintVersion LNL.Var = P.Var
  toPrintable (LNL.LambdaVar i) = P.LambdaVar i
  toPrintable (LNL.LetVar i1 i2) = P.LetVar i1 i2
  toPrintable (LNL.CaseConstructorVar i1 i2) = P.CaseConstructorVar i1 i2
  toPrintable (LNL.FreeVar name) = P.FreeVar name

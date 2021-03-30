module LanguageLogic (impRelImplies) where

{- This file contains logic specific to space improvement theory. It does
however not contain the logic for the binding structure. This is handled in the
other files. It might be that these functions might be implemented as parsed
in the laws file later.
-}

import qualified MiniTypedAST as T
import qualified AbsSie as UT

class ImpRelRepresentation a where
  -- | If given two improvement relations I1 ans I2 (<~>, <~~>, |~>, |~~>, =def=
  -- <̣~| or <~~|) the function returns wether I1 -> I2, i.e. whether
  -- forall M, N. M I1 N -> M I2 N
  impRelImplies :: a -> a -> Bool

-- TODO expand as T.ImpRel adds more relations
instance ImpRelRepresentation T.ImpRel where
  impRelImplies i1 i2 | i1 == i2 = True

instance ImpRelRepresentation UT.ImpRel where
  {-
  a a       = True
  =def= _   = True
  <~> =def= = False
  <~> _     = True
  |~> |~~>  = True
  <~| <~~|  = True
  <~~> <~~| = True
  <~~> |~~> = True
  _ _ = False
  -}
  impRelImplies i1 i2 | i1 == i2 = True
  impRelImplies UT.DefinedEqual _ = True
  impRelImplies UT.StrongCostEquiv UT.DefinedEqual = False
  impRelImplies UT.StrongCostEquiv _ = True
  impRelImplies UT.StrongImprovementLR UT.WeakImprovementLR = True
  impRelImplies UT.StrongImprovementRL UT.WeakImprovementRL = True
  impRelImplies UT.WeakCostEquiv UT.StrongCostEquiv = False
  impRelImplies UT.WeakCostEquiv UT.WeakImprovementLR = True
  impRelImplies UT.WeakCostEquiv UT.WeakImprovementRL = True
  impRelImplies _ _ = False

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module LanguageLogic (impRelImplies
                     , reduce) where

{- This file contains logic specific to space improvement theory. It does
however not contain the logic for the binding structure. This is handled in the
other files. It might be that these functions might be implemented as parsed
in the laws file later.
note that the name for true, false, cons and nil
are in Common.hs for inheritance reasons.
-}

import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Except (MonadError)
import Data.List (find, intersperse)

import qualified Common as Com
import qualified AbsSie as UT
import qualified MiniTypedAST as T
import TermUtils (substituteFor)
import CheckMonad (throwCallstackError, assert, internalException)
import TermCorrectness (isValue)
import OtherUtils (distinct)
import ShowTypedTerm (showTypedTerm)
import Common (trueName, falseName)

class ImpRelRepresentation a where
  -- | If given two improvement relations I1 ans I2 (<~>, <~~>, |~>, |~~>, =def=
  -- <̣~| or <~~|) the function returns wether I1 -> I2, i.e. whether
  -- forall M, N. M I1 N -> M I2 N
  impRelImplies :: a -> a -> Bool

-- TODO expand as T.ImpRel adds more relations
instance ImpRelRepresentation Com.ImpRel where
  impRelImplies i1 i2 = toUT i1 `impRelImplies` toUT i2
    where
      toUT :: Com.ImpRel -> UT.ImpRel
      toUT Com.DefinedEqual = UT.DefinedEqual
      toUT Com.StrongImprovementLR = UT.StrongImprovementLR
      toUT Com.WeakImprovementLR = UT.WeakImprovementLR
      toUT Com.StrongCostEquiv = UT.StrongCostEquiv
      toUT Com.WeakCostEquiv = UT.WeakCostEquiv

instance ImpRelRepresentation UT.ImpRel where
  {-
  a a       = True
  =def= _   = True
  <~> =def= = False
  <~> _     = True
  |~> |~~>  = True
  <~~> |~~> = True
  _ _ = False
  -}
  impRelImplies i1 i2 | i1 == i2 = True
  impRelImplies UT.DefinedEqual _ = True
  impRelImplies UT.StrongCostEquiv UT.DefinedEqual = False
  impRelImplies UT.StrongCostEquiv _ = True
  impRelImplies UT.StrongImprovementLR UT.WeakImprovementLR = True
  impRelImplies UT.WeakCostEquiv UT.StrongCostEquiv = False
  impRelImplies UT.WeakCostEquiv UT.WeakImprovementLR = True
  impRelImplies _ _ = False

-- | given R and V, returns N such that R[V] ~~> N, where ~~> is reduction.
-- R is a reduction, since the weight is needed to make it into
-- a term, and that is not specific to the reduction.
-- note that R must be a reduction context and V must be a value.
-- the monad is for input checking in substitution.
-- Throws an error if the reduction is unsuccessful.
reduce :: (HasCallStack, Log.MonadLogger m, MonadError String m) =>
          T.Red -> T.Term -> m T.Term
reduce (T.RApp T.THole y) (T.TLam x term) = substituteFor term y x
reduce (T.RCase T.THole branches) (T.TConstructor cj ys) =
  case find (\(ci, _,_) -> ci == cj) branches of
    Just (_cj, xsj, tMj) -> do
      substituteAll tMj ys xsj
      where
        substituteAll term [] [] = return term
        substituteAll term (y:ys) (x:xs) = do
          term' <- substituteFor term y x
          substituteAll term' ys xs
        substituteAll _ _ _ = internalException
                                "substitution params not same length."
    Nothing -> throwCallstackError $ "reduction not possible. "++cj++" is "
      ++"not one of the possible cases in "++names
      where names = let (cNames, _, _) = unzip3 branches
                    in concat $ intersperse ", " cNames
reduce (T.RSeq T.THole tM) tV = do
  assert (isValue tV)
    $ "in seq V M, V must be a value. V="++showTypedTerm tV
  return tM
reduce (T.RPlusWeight T.THole w tN) (T.TNum m) =
  return $ T.TRedWeight w (T.RAddConst m tN)
reduce (T.RAddConst m T.THole) (T.TNum n) = return $ T.TNum (m + n)
reduce (T.RIsZero T.THole) (T.TNum m)
  | m == 0 = return $ T.TConstructor trueName []
  | otherwise = return $ T.TConstructor falseName []
reduce rR tV = throwCallstackError $ "Reduction failed. Type error in inputs "
  ++"R = "++showTypedTerm (T.TRedWeight 1 rR)++" and V="++showTypedTerm tV

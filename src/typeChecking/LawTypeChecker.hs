{-# LANGUAGE TypeFamilies #-}

module LawTypeChecker (typecheckLaws) where

import qualified AbsSieLaws as UT
import qualified TypedLawAST as T
import CheckMonad (CheckM, runCheckM, assert, assertInternal)

typecheckLaws :: UT.LawList -> Either [String] T.LawMap
typecheckLaws lawList = undefined --runCheckM typecheckLaws'
  where
    --typecheckLaws' = do
    --  tLawList <- mapM transform lawList
    --  return undefined



class Transformable a where
  type TypedVersion a
  transform :: a -> CheckM (TypedVersion a)

instance Transformable UT.Law where
  type TypedVersion UT.Law = T.Law
  transform = undefined

checkLaw :: T.Law -> CheckM ()
checkLaw = undefined

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module LawTypeChecker (typecheckLaws) where

import qualified AbsSieLaws as UT
import qualified TypedLawAST as T
import CheckMonad (CheckM, runCheckM, assert, assertInternal)
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as Map
import Common (ImpRel)

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
    UT.TValueMetaVar mVValue -> throwError "TValueMetaVar not supported yet"
    UT.TGeneralMetaVar mvTerm -> throwError "TGeneralMetaVar not supported yet"
    UT.TVar var -> throwError "TVar not supported yet"
    UT.TAppCtx mvContext term -> throwError "TAppCtx not supported yet"
    UT.TAppValCtx mVValueContext term ->
      throwError "TAppValCtx not supported yet"
    UT.TNonTerminating -> throwError "TNonTerminating not supported yet"
    UT.TNum integer -> throwError "TNum not supported yet"
    UT.TIndVar var indExpr -> throwError "TIndVar not supported yet"
    UT.TConstructor constructor -> throwError "TConstructor not supported yet"
    UT.TStackSpike term -> throwError "TStackSpike not supported yet"
    UT.TStackSpikes stackWeight term ->
      throwError "TStackSpikes not supported yet"
    UT.THeapSpike term -> throwError "THeapSpike not supported yet"
    UT.THeapSpikes heapWeight term -> throwError "THeapSpikes not supported yet"
    UT.TDummyBinds varSet term -> throwError "TDummyBinds not supported yet"
    UT.TRedMetaVar mvReduction term ->
      throwError "TRedMetaVar not supported yet"
    UT.TRedMetaVarW redWeight mvReduction term ->
      throwError "TRedMetaVarW not supported yet"
    UT.TSubstitution term v1 v2 -> throwError "TSubstitution not supported yet"
    UT.TRApp term var -> throwError "TRApp not supported yet"
    UT.TRAppW rw term var -> throwError "TRAppW not supported yet"
    UT.TRPlus term1 term2 -> throwError "TRPlus not supported yet"
    UT.TRPlusW1 rw term1 term2 -> throwError "TRPlusW1 not supported yet"
    UT.TRPlusW2 term1 rw term2 -> throwError "TRPlusW2 not supported yet"
    UT.TRPlusWW rw1 term1 rw2 term2 -> throwError "TRPlusWW not supported yet"
    UT.TLam var term -> throwError "TLam not supported yet"
    UT.TLet lbs term -> throwError "TLet not supported yet"
    UT.TRCase mRw term caseStms -> throwError "TRCase not supported yet"
    UT.TRAddConst mRw integer term -> throwError "TRAddConst not supported yet"
    UT.TRIsZero mRw term -> throwError "TRIsZero not supported yet"
    UT.TRSeq mRw term1 term2 -> throwError "TRSeq not supported yet"

transformImpRel :: UT.ImpRel -> CheckM (ImpRel, Bool)
transformImpRel = undefined

instance Transformable UT.SideCond where
  type TypedVersion UT.SideCond = T.SideCond
  transform = undefined

------------------------Checking
checkLaw :: T.Law -> CheckM ()
checkLaw = undefined

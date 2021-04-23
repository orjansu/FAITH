{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Substitution (applySubstitution) where

import Data.Text (pack, Text)
import Data.List (intersperse)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import CheckMonad (CheckM, runCheckM, assert, assertInternal, internalException)
import qualified Control.Monad.Logger as Log
import Control.Monad.Except (MonadError, throwError)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables
                       , checkTypedTerm, numHoles)
import ShowTypedTerm (showTypedTerm)
import ToLocallyNameless (toLocallyNameless)

type IsUsed = Bool
data SubstSt = MkSubstSt
  { substitutions :: Map.Map String (T.Substitute, IsUsed)
  , forbiddenNames :: Set.Set String
  }

newtype SubstM a = MkSubstM {getSubstM :: (StateT SubstSt CheckM a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String
           , MonadState SubstSt)

instance MonadFail SubstM where
  fail str = internalException str


-- | Given M, sigma and S, where M is a law term with meta-
-- variables, sigma is a substitution that substitutes all meta-
-- variables for concrete variables and S is a set of variable names,
-- this function returns sigma applied to M, such that the names of the bound
-- variables in the result are unique, both with respect to the result term
-- and the variable names in S.
--
-- Fails if sigma doesn't contain substitutions for all meta-variables in M.
applySubstitution :: Law.Term
                  -> T.Substitutions
                  -> Set.Set String
                  -> CheckM T.Term
applySubstitution law substSimpleMap initForbiddenNames = do
  Log.logInfoN . pack $ "applying substitution {"++showSubstitutions++"}"
  Log.logInfoN . pack $ "to law term"++show law
  Log.logInfoN . pack $ "With forbidden names "++ show initForbiddenNames
  -- TODO revise using SubstitutionMonad
  let substMap = Map.map (\substitution -> (substitution, False)) substSimpleMap
      initSt = MkSubstSt {substitutions = substMap
                         , forbiddenNames = initForbiddenNames}
  finalTerm <- (flip evalStateT) initSt $ getSubstM $ substLawTerm law
  checkTypedTerm finalTerm initForbiddenNames
  return finalTerm
  where
    showSubstitutions = concat $
                          intersperse "," $
                            map showSingle $
                              Map.toList substSimpleMap
    showSingle (name, subst) = name ++ " -> "++showSubstitute subst
    showSubstitute = \case
      T.SLetBindings letBindings ->
        showTypedTerm (T.TLet letBindings (T.TNum 1)) -- for now
      T.SValue term -> showTypedTerm term
      T.SContext term -> showTypedTerm term
      T.SIntegerVar intExpr -> case intExpr of
        T.IENum n -> show n
      T.SVar string -> string
      T.SVarSet stringSet ->
        let listForm = concat . intersperse ", " . Set.toList $ stringSet
        in "{" ++ listForm ++"}"

substLawTerm :: Law.Term -> SubstM T.Term
substLawTerm = \case
  Law.TValueMetaVar valueMV -> do
    (T.SValue valueTerm, _) <- getSubstitute valueMV
    return valueTerm
  Law.TVar varMV -> do
    (T.SVar varName, _) <- getSubstitute varMV
    return $ T.TVar varName
  Law.TAppCtx ctxMV term -> do
    (T.SContext ctx, wasUsed) <- getSubstitute ctxMV
    sTerm <- substLawTerm term
    substituteContext ctx sTerm wasUsed
  Law.TLet letBindings term -> undefined
  Law.TDummyBinds varSet term -> undefined

-- | fetches the substitute and returns the potentially renamed version of it,
-- and a bool that is true if it was used before this substitution.
getSubstitute :: String -> SubstM (T.Substitute, Bool)
getSubstitute metaVar = do
  substMap <- gets substitutions
  case Map.lookup metaVar substMap of
    Just (subst, isUsed) ->
      case subst of
        T.SLetBindings letBindings -> undefined
        T.SValue term -> do
          prepared <- prepareTermForSubstitution metaVar term isUsed
          return $ (T.SValue prepared, isUsed)
        T.SContext ctx -> do
          prepared <- prepareTermForSubstitution metaVar ctx isUsed
          return $ (T.SValue prepared, isUsed)
        T.SIntegerVar intExpr -> undefined
        T.SVar string -> return $ (T.SVar string, isUsed)
        T.SVarSet varSet -> undefined
    Nothing -> throwError $ "Substitution for "++metaVar++" not found"

-- | given C and M, substitutes M into C, and does the neccecary checks for
-- correctess of the current support for contexts.
substituteContext :: T.Term -> T.Term -> Bool -> SubstM T.Term
substituteContext context term wasUsed = do
  insertedTerm <- insertTerm context term
  if wasUsed
    then let (_lnlctx, ctxFV) = toLocallyNameless context
             (_lnlterm, termFV) = toLocallyNameless term
             (_lnlInserted, insertedFV) = toLocallyNameless insertedTerm
         in assert ((ctxFV `Set.union` termFV) == insertedFV)
              $ "The insertion of "++showTypedTerm term++" into "
                ++showTypedTerm context++" should not capture any variables."
    else return ()
  return insertedTerm
  where
    -- | Constructs an infinite list of
    substitutionTerms :: T.Term -> Set.Set String -> [T.Term]
    substitutionTerms origTerm forbidden = origTerm : renamedVersions
      where
        renamedVersions =
          let (nextTerm, forbidden') = renameAllBound origTerm forbidden
              nextTerms = substitutionTerms origTerm forbidden'
          in nextTerm : nextTerms

    -- C -> M -> has-M-been-used-before -> forbiddenNames
    insertTerm = undefined -- :: T.Term -> T.Term -> Bool -> Set.Set String

-- | TODO remove
prepareTermForSubstitution :: String -> T.Term -> Bool -> SubstM T.Term
prepareTermForSubstitution metaVar term isUsed =
  if isUsed
    then do
      forbidden <- gets forbiddenNames
      renamed <- renameNeeded term forbidden
      assertInternal (getBoundVariables renamed `Set.disjoint`
                      getBoundVariables term)
        $ "bound variables of used term or context "++showTypedTerm term
          ++" when renamed to "++showTypedTerm renamed
          ++" should rename all bound variables so "
          ++show (getBoundVariables renamed `Set.intersection`
            getBoundVariables term)++" should be empty."
      let newBoundVars = getBoundVariables renamed
          forbidden' = newBoundVars `Set.union` forbidden
      modify (\st -> st{forbiddenNames = forbidden'})
      return renamed
    else do
      forbidden <- gets forbiddenNames
      let termBV = getBoundVariables term
      assertInternal (termBV `Set.disjoint` forbidden)
        $ "term or context M inserted the first time should only contain new "
          ++"names for bound variables. M="++showTypedTerm term
      substMap <- gets substitutions
      let forbidden' = termBV `Set.union` forbidden
          setToUsed = (\(t, False) -> (t, True))
          substMap' = Map.adjust setToUsed metaVar substMap
      modify (\st -> st{forbiddenNames = forbidden'
                       , substitutions = substMap'})
      return term

-- | could be defined in terms of renameNeeded
renameAllBound :: T.Term -> Set.Set String -> (T.Term, Set.Set String)
renameAllBound term forbidden = undefined

-- | given a term M and a set of variables S, returns M, where all bound
-- variables in M are distinct from the variables in S
-- Assumes that the names of the bound variables in M are distinct
renameNeeded :: (MonadError String m) => T.Term -> Set.Set String -> m T.Term
renameNeeded term forbiddenNames = do
  checkBoundVariablesDistinct term
  case term of
    T.TVar var -> undefined
    T.TNum integer -> undefined
    T.TLam var term -> undefined
    T.THole -> undefined
    T.TLet letBindings term -> undefined
    T.TDummyBinds varSet term -> undefined
    T.TRedWeight redWeight red -> undefined

-- | given M, v1 and v2, where M is a term, and v1 and v2 are names, replaces
-- every mention of v1 with v2.
renameSingle :: T.Term -> String -> String -> CheckM T.Term
renameSingle term oldName newname = undefined

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
import CheckMonad (CheckM, runCheckM, assert, assertInternal)
import qualified Control.Monad.Logger as Log
import Control.Monad.Except (MonadError, throwError)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables
                       , checkTypedTerm, numHoles)

import ShowTypedTerm (showTypedTerm)

type IsUsed = Bool
data SubstSt = MkSubstSt
  { substitutions :: Map.Map String (T.Substitute, IsUsed)
  , forbiddenNames :: Set.Set String
  }

newtype SubstM a = MkSubstM {getSubstM :: (StateT SubstSt CheckM a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String
           , MonadState SubstSt)

instance MonadFail SubstM where
  fail str = throwError str


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
  let substMap = Map.map (\substitution -> (substitution, False)) substSimpleMap
      initSt = MkSubstSt {substitutions = substMap
                         , forbiddenNames = initForbiddenNames}
  (flip evalStateT) initSt $ getSubstM $ substLawTerm law
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
        T.SValue valueTerm <- getSubstitute valueMV
        return valueTerm
      Law.TVar var -> undefined
      Law.TAppCtx ctxMV term -> undefined
      Law.TLet letBindings term -> undefined
      Law.TDummyBinds varSet term -> undefined

    getSubstitute :: String -> SubstM T.Substitute
    getSubstitute metaVar = do
      substMap <- gets substitutions
      case Map.lookup metaVar substMap of
        Just (subst, isUsed) ->
          case subst of
            T.SLetBindings letBindings -> undefined
            T.SValue term -> do
              prepared <- prepareTermForSubstitution metaVar term isUsed
              return $ T.SValue prepared
            T.SContext term -> undefined
            T.SIntegerVar intExpr -> undefined
            T.SVar string -> undefined
            T.SVarSet varSet -> undefined
        Nothing -> throwError $ "Substitution for "++metaVar++" not found"

    prepareTermForSubstitution :: String -> T.Term -> Bool -> SubstM T.Term
    prepareTermForSubstitution metaVar term isUsed =
      if isUsed
        then do
          forbidden <- gets forbiddenNames
          renamed <- renameNeeded term forbidden
          assertInternal (getBoundVariables renamed `Set.disjoint`
                          getBoundVariables term)
            $ "bound variables of used term "++showTypedTerm term
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
            $ "term M inserted the first time should only contain new "
              ++"names for bound variables. M="++showTypedTerm term
          substMap <- gets substitutions
          let forbidden' = termBV `Set.union` forbidden
              setToUsed = (\(t, False) -> (t, True))
              substMap' = Map.adjust setToUsed metaVar substMap
          modify (\st -> st{forbiddenNames = forbidden'
                           , substitutions = substMap'})
          return term

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

-- | Given a variable name v and a set of forbidden names S, returns a new
-- variable name v' that is similar to v, but not in S.
--
-- Throws an error if v is not in S, i.e. if the renaming is not needed.
--
-- TODO: might be more user friendly to add an increasing index at the end of
-- the name. For now, I'll just get a fresh letter from the alphabet.
freshName :: String -> Set.Set String -> CheckM String
freshName name forbiddenNames = do
  assertInternal (Set.notMember name forbiddenNames) $ "Renaming was "
    ++"attempted, but not needed"
  return $ freshName' 0
  where
    freshName' n = let tryName = freshNames !! n
                   in if Set.notMember tryName forbiddenNames
                        then tryName
                        else freshName' (n+1)

    alphabet :: String
    alphabet = "abcdefghijklmnopqrstuvxyz"
    -- ["a","b","c"] etc
    firstNames :: [String]
    firstNames = map (:[]) alphabet

    genNames :: [String] -> [String]
    genNames prev = [a++[b] | a <- prev, b <- alphabet]

    -- | names of length n.
    -- So if the alphabet would be "abc"
    -- lenNames 0 = ["a","b","c"]
    -- lenNames 1 = ["aa","ab","ac","ba","bb","bc","ca","cb","cc"]
    -- etc
    lenNames :: Integer -> [String]
    lenNames 0 = firstNames
    lenNames n = genNames $ lenNames $ n-1

    -- | Returns an infinite list of fresh names in the style
    -- a,b,c,...,ba,bb,bc,...ca,cb,cc,...aaa
    freshNames :: [String]
    freshNames = foldr (++) [] $ map lenNames [0..]

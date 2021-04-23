{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A monad with the invariant that all terms that you get out of the
-- substitutionMonad are properly renamed so that their bound variables
-- are distinct from the other bound variables from terms that are
-- previously gotten out of the monad and the initial set of forbidden
-- names.
module SubstitutionMonad (runSubstM
                         , getSubstitute
                         , applyContext) where

import qualified Data.Map.Strict as Map -- TODO fundera om lat är bättre
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified Control.Monad.State as State (lift)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, ask, runReaderT, ReaderT)
import CheckMonad (CheckM, runCheckM, assert, assertInternal, internalException)
import qualified Control.Monad.Logger as Log
import Control.Monad.Trans.Class (MonadTrans)
import Data.List (zip4, unzip4)

import qualified MiniTypedAST as T
import ShowTypedTerm (showTypedTerm)
import TermCorrectness (getBoundVariables, numHoles
                       , checkBoundVariablesDistinct)
import OtherUtils (applyOnSubTermsM)

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

-- | Given the substitutions, an initial set of forbidden names and a monadic
-- computation, this function returns the result of the monadic computation,
-- along with the final set of forbidden names. It is still in the CheckM
-- though, since most of the other parts of the program is.
--
-- NOTE: the initial set of forbidden names must include the free variables
-- of the term about to be transformed.
-- Since the typechecker should have checked that all substitutions are
-- provided, the function throws internal exceptions if they are not.
runSubstM :: Map.Map String T.Substitute -> Set.Set String -> SubstM a
             -> CheckM (a, Set.Set String)
runSubstM substSimpleMap initForbiddenNames monadic = do
  let substMap = prepareSubstitutions substSimpleMap
      initSt = MkSubstSt {substitutions = substMap
                         , forbiddenNames = initForbiddenNames}
  (a, finalState) <- (flip runStateT) initSt $ getSubstM $ monadic
  return (a, forbiddenNames finalState)

prepareSubstitutions :: Map.Map String T.Substitute
                        -> Map.Map String (T.Substitute, IsUsed)
prepareSubstitutions substSimpleMap =
  Map.map (\substitution -> (substitution, False)) substSimpleMap

-- | Get the substitution corresponding to the name provided. Does not work for
-- contexts. If you would like to apply a context, use applyContext instead.
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
        T.SContext ctx -> internalException $ "use applyContext, not "
                            ++"getSubstitute for contexts"
        T.SIntegerVar intExpr -> case intExpr of
          T.IENum _ -> return subst
        T.SVar string -> return $ T.SVar string
        T.SVarSet varSet -> undefined
        T.STerm term -> do
          prepared <- prepareTermForSubstitution metaVar term isUsed
          return $ T.STerm prepared
    Nothing -> internalException $ "Substitution for "++metaVar++" not found"

prepareTermForSubstitution :: String -> T.Term -> Bool -> SubstM T.Term
prepareTermForSubstitution metaVar term isUsed =
  if isUsed
    then do
      forbidden <- gets forbiddenNames
      renamed <- renameAllBound term forbidden
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

-- | given a name corresponding to a context C and a term M, returns C[M].
--
applyContext :: String -> T.Term -> SubstM T.Term
applyContext ctxName term = do
  assertInternal (numHoles term == 0)
    "You may not insert a context into a context"
  substMap <- gets substitutions
  Just (T.SContext ctx, isUsed) <- return $ Map.lookup ctxName substMap
  if isUsed
    then do
      appliedButWithOldNames <- applyContext1 ctx term
      --appliedWithNewNames <- renameAllBound appliedButWithOldNames
      undefined
    else applyContext1 ctx term

  where
    applyContext1 :: T.Term -> T.Term -> SubstM T.Term
    applyContext1 ctx term = do
      let substitutions = Map.singleton dummy (T.STerm term)
      withSeparateSubstitutions substitutions $ applyContext2 ctx

    dummy :: String
    dummy = ""

    applyContext2 :: T.Term -> SubstM T.Term
    applyContext2 = \case
      T.TVar var -> return $ T.TVar var
      T.TNum integer -> return $ T.TNum integer
      T.THole -> do
        T.STerm substTerm <- getSubstitute dummy
        return substTerm
      recursiveTerm -> applyOnSubTermsM applyContext2 recursiveTerm

-- | Run the monadic computation with a new substitution set, and then
-- switch back.
withSeparateSubstitutions :: Map.Map String T.Substitute
                     -> SubstM a
                     -> SubstM a
withSeparateSubstitutions simpleInternalSubstitutions monadic = do
  currSubstitutions <- gets substitutions
  let internalSubstitutions = prepareSubstitutions simpleInternalSubstitutions
  modify (\st -> st{substitutions = internalSubstitutions})
  res <- monadic
  modify (\st -> st{substitutions = currSubstitutions})
  return res

-- | given M and S, renames all bound variables in M such that the new variables
-- are distinct from the set of forbidden names S. Does not rename or change
-- weights.
--
-- Note: a variation would be to return the new set of forbidden names, or the
-- set of new names, but running getAllMetaVars is O(n) anyways, so I skip this,
-- at least for now.
renameAllBound :: (Log.MonadLogger m, MonadError String m) =>
                  T.Term -> Set.Set String -> m T.Term
renameAllBound term1 forbidden = do
  checkBoundVariablesDistinct term1
  let initBV = getBoundVariables term1
  term2 <- (flip evalStateT) Map.empty
             $(flip runReaderT) forbidden
               $ renameAllBoundMonadic term1
  let newBV = getBoundVariables term2
  assertInternal (initBV `Set.disjoint` newBV)
    "Renaming all variables should change all bound variables."
  return term2

renameAllBoundMonadic :: (MonadState (Map.Map String String) m,
                          MonadReader (Set.Set String) m,
                          Log.MonadLogger m, MonadError String m) =>
                    T.Term -> m T.Term
renameAllBoundMonadic = \case
  T.TVar var -> do
    var' <- toCorrectMentionedVar var
    return $ T.TVar var
  T.TNum integer -> return $ T.TNum integer
  T.TLam var term -> do
    var' <- toCorrectBoundVar var
    term' <- renameAllBoundMonadic term
    return $ T.TLam var' term
  T.THole -> return $ T.THole
  T.TLet letBindings1 mainTerm1 -> do
    let (bindingVars1, sWeights1, hWeights1, boundTerms1) = unzip4 letBindings1
    bindingVars2 <- mapM toCorrectBoundVar bindingVars1
    boundTerms2 <- mapM renameAllBoundMonadic boundTerms1
    mainTerm2 <- renameAllBoundMonadic mainTerm1
    let letBindings2 = zip4 bindingVars2 sWeights1 hWeights1 boundTerms2
    return $ T.TLet letBindings2 mainTerm2
  T.TDummyBinds varSet1 term1 -> do
    let varList1 = Set.toList varSet1
    varList2 <- mapM toCorrectMentionedVar varList1
    let varSet2 = Set.fromList varList2
    term2 <- renameAllBoundMonadic term1
    return $ T.TDummyBinds varSet2 term2
  T.TRedWeight rw1 red1 -> do
    red2 <- case red1 of
              T.RApp term1 var1 -> do
                var2 <- toCorrectMentionedVar var1
                term2 <- renameAllBoundMonadic term1
                return $ T.RApp term2 var2
              T.RPlusWeight t1 rw2 t2 -> do
                t1' <- renameAllBoundMonadic t1
                t2' <- renameAllBoundMonadic t2
                return $ T.RPlusWeight t1' rw2 t2'
    return $ T.TRedWeight rw1 red2


toCorrectMentionedVar :: (MonadState (Map.Map String String) m)
                          => String -> m String
toCorrectMentionedVar var = do
  renameMap <- get
  case Map.lookup var renameMap of
    Just newName -> return newName
    Nothing -> return var

toCorrectBoundVar :: (MonadState (Map.Map String String) m,
                      MonadReader (Set.Set String) m,
                      Log.MonadLogger m, MonadError String m)
                      => String -> m String
toCorrectBoundVar oldName = do
  forbiddenNames <- ask
  assertInternal (oldName `Set.member` forbiddenNames)
    "All bound variables should need to be renamed."
  newName <- freshName oldName forbiddenNames
  renameMap <- get
  assertInternal (oldName `Map.notMember` renameMap)
    "Old names should not be renamed twice, since binders are unique"
  let renameMap' = Map.insert oldName newName renameMap
  put renameMap'
  return newName

-- | Given a variable name v and a set of forbidden names S, returns a new
-- variable name v' that is similar to v, but not in S.
--
-- Throws an error if v is not in S, i.e. if the renaming is not needed.
--
-- TODO: might be more user friendly to add an increasing index at the end of
-- the name. For now, I'll just get a fresh letter from the alphabet.
freshName :: (Log.MonadLogger m, MonadError String m) =>
             String -> Set.Set String -> m String
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

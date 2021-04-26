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
                         , applyContext
                         , SubstM) where

import qualified Data.Map.Strict as Map -- TODO fundera om lat är bättre
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import qualified Control.Monad.State as State (lift)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, ask, runReaderT, ReaderT)
import CheckMonad (CheckM, runCheckM, assert, assertInternal, internalException)
import Data.Text (pack)
import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack)
import Control.Monad.Trans.Class (MonadTrans)
import Data.List (zip4, unzip4)

import qualified MiniTypedAST as T
import ShowTypedTerm (showTypedTerm)
import TermCorrectness (getBoundVariables, numHoles, getFreeVariables
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
-- NOTE: The forbidden names set is used for making sure that new names that
-- are used when a term is alpha-renamed doesn't accidentally clash with other
-- names in the term. Therefore:
--  > the initial set of forbidden names must include the free variables
--    of the term about to be transformed.
--  > The forbidden names must also include all the variables that should be
--    substituted into a binding position, e.g. the name x, y, z and zs in the
--    term
--    \x . let y = x:[]
--         in case y of
--           z:zs -> 1
--
-- Since the typechecker should have checked that all substitutions are
-- provided, the function throws internal exceptions if they are not.
runSubstM :: HasCallStack =>
             Map.Map String T.Substitute -> Set.Set String -> SubstM a
             -> CheckM (a, Set.Set String)
runSubstM substSimpleMap initForbiddenNames monadic = do
  let substMap = prepareSubstitutions substSimpleMap
      initSt = MkSubstSt {substitutions = substMap
                         , forbiddenNames = initForbiddenNames}
  (a, finalState) <- (flip runStateT) initSt $ getSubstM $ do
    addContextBVToForbiddenNames
    monadic
  let finalForbiddenNames = forbiddenNames finalState
  assertInternal (initForbiddenNames `Set.isSubsetOf` finalForbiddenNames)
    "Substitution map should only accumulate forbidden names."
  return (a, finalForbiddenNames)
  where
    addContextBVToForbiddenNames =
      mapM addBVToForbiddenNames
        $ map (\(T.SContext ctx) -> ctx)
        $ Map.elems
        $ Map.filter isContext substSimpleMap
    isContext :: T.Substitute -> Bool
    isContext (T.SLetBindings _) = False
    isContext (T.SValue _) = False
    isContext (T.SContext _) = True
    isContext (T.SIntegerVar _) = False
    isContext (T.SVar _) = False
    isContext (T.SVarSet _) = False
    isContext (T.STerm _) = False

prepareSubstitutions :: HasCallStack => Map.Map String T.Substitute
                        -> Map.Map String (T.Substitute, IsUsed)
prepareSubstitutions substSimpleMap =
  Map.map (\substitution -> (substitution, False)) substSimpleMap

-- | Get the substitution corresponding to the name provided.
-- > Does not work for contexts. If you would like to apply a context, use
--   applyContext instead.
getSubstitute :: HasCallStack => String -> SubstM T.Substitute
getSubstitute metaVar = do
  substMap <- gets substitutions
  case Map.lookup metaVar substMap of
    Just (subst, isUsed) ->
      case subst of
        T.SLetBindings letBindings1 -> do
          let asTerm = T.TLet letBindings1 (T.TNum 0)
          preparedTerm <- prepareTermForSubstitution metaVar asTerm isUsed
          T.TLet letBindings2 (T.TNum 0) <- return preparedTerm
          return $ T.SLetBindings letBindings2
        T.SValue term -> do
          prepared <- prepareTermForSubstitution metaVar term isUsed
          return $ T.SValue prepared
        T.SContext ctx -> internalException $ "use applyContext, not "
                            ++"getSubstitute for contexts"
        T.SIntegerVar intExpr -> case intExpr of
          T.IENum _ -> return subst
        T.SVar string -> return $ T.SVar string
        T.SVarSet varSet -> return $ T.SVarSet varSet
        T.STerm term -> do
          prepared <- prepareTermForSubstitution metaVar term isUsed
          return $ T.STerm prepared
    Nothing -> internalException $ "Substitution for "++metaVar++" not found"

prepareTermForSubstitution :: HasCallStack =>
                              String -> T.Term -> Bool -> SubstM T.Term
prepareTermForSubstitution metaVar term isUsed =
  if isUsed
    then do
      renamed <- renameAllBound term
      return renamed
    else do
      setToUsed metaVar
      let termBV = getBoundVariables term
      forbidden <- gets forbiddenNames
      assertInternal (termBV `Set.disjoint` forbidden)
        $ "term M inserted the first time should only contain new "
          ++"names for bound variables. M="++showTypedTerm term
      addBVToForbiddenNames term
      return term

-- | given a substitution name, sets the substitution to used.
setToUsed :: HasCallStack => String -> SubstM ()
setToUsed metaVar = do
  substMap <- gets substitutions
  let flipToUsed = (\(t, False) -> (t, True))
      substMap' = Map.adjust flipToUsed metaVar substMap
  modify (\st -> st{ substitutions = substMap'})

addBVToForbiddenNames :: HasCallStack => T.Term -> SubstM ()
addBVToForbiddenNames term = do
  forbidden <- gets forbiddenNames
  let termBV = getBoundVariables term
      forbidden' = termBV `Set.union` forbidden
  modify (\st -> st{forbiddenNames = forbidden'})

-- | given a name corresponding to a context C and a term M, returns C[M],
-- properly renamed.
applyContext :: HasCallStack => String -> T.Term -> SubstM T.Term
applyContext ctxName term = do
  assertInternal (numHoles term == 0)
    "You may not insert a context into a context"
  substMap <- gets substitutions
  Just (T.SContext ctx, isUsed) <- return $ Map.lookup ctxName substMap
  if isUsed
    then do
      appliedButWithOldNames <- applyContext1 ctx term
      appliedWithNewNames <- renameNeeded appliedButWithOldNames
      return appliedWithNewNames
    else do
      res <- applyContext1 ctx term
      addBVToForbiddenNames res
      setToUsed ctxName
      return res

  where
    applyContext1 :: HasCallStack => T.Term -> T.Term -> SubstM T.Term
    applyContext1 ctx term = do
      let substitutions = Map.singleton dummy (T.STerm term, True)
      -- We set the inner term to used, so that the bound variables in the term
      -- will be renamed, in case the term or some subterm of it is used
      -- before or after the context is used.
      withSeparateSubstitutions substitutions $ applyContext2 ctx

    dummy :: String
    dummy = ""

    applyContext2 :: HasCallStack => T.Term -> SubstM T.Term
    applyContext2 = \case
      T.TVar var -> return $ T.TVar var
      T.TNum integer -> return $ T.TNum integer
      T.THole -> do
        T.STerm substTerm <- getSubstitute dummy
        return substTerm
      recursiveTerm -> applyOnSubTermsM applyContext2 recursiveTerm

-- | Run the monadic computation with a new substitution set, and then
-- switch back.
withSeparateSubstitutions :: HasCallStack =>
                     Map.Map String (T.Substitute, IsUsed)
                     -> SubstM a
                     -> SubstM a
withSeparateSubstitutions internalSubstitutions monadic = do
  currSubstitutions <- gets substitutions
  modify (\st -> st{substitutions = internalSubstitutions})
  res <- monadic
  modify (\st -> st{substitutions = currSubstitutions})
  return res

liftCheckM :: CheckM a -> SubstM a
liftCheckM checkMonadic = MkSubstM{getSubstM = State.lift checkMonadic}


-- | given M, this function assumes (and checks) that all bound variables in M
-- needs to be renamed, renames those terms, changes the forbiddenNames
-- accordingly and returns the renamed term.
renameAllBound :: HasCallStack => T.Term -> SubstM T.Term
renameAllBound term1 = do
  let initBV = getBoundVariables term1
  term2 <- renameNeeded term1
  let newBV = getBoundVariables term2
  assertInternal (initBV `Set.disjoint` newBV)
    "Renaming all bound variables should change all bound variables."
  return term2

-- | given M, renames all bound variables in M that need to be renamed.
renameNeeded :: HasCallStack => T.Term -> SubstM T.Term
renameNeeded term1 = do
  let initBV = getBoundVariables term1
      initFV = getFreeVariables term1

  forbiddenNames1 <- gets forbiddenNames
  let shouldBeUnchanged = initBV Set.\\ forbiddenNames1
  term2 <- runRenameNeeded term1 forbiddenNames1
  Log.logInfoN . pack $ "Checking correctness of renaming "
    ++showTypedTerm term1++" to "++showTypedTerm term2
  let newBV = getBoundVariables term2
      forbiddenNames2 = newBV `Set.union` forbiddenNames1
  modify (\st -> st{forbiddenNames = forbiddenNames2})

  let unchanged = newBV Set.\\ forbiddenNames2
  assertInternal (unchanged == shouldBeUnchanged) $
    "Renaming just needed variables should not rename variables that do not "
    ++"need to be renamed. "++show unchanged++" /= "++show shouldBeUnchanged
  assertInternal (newBV `Set.disjoint` forbiddenNames1) $
    "Renaming needed variables should rename all variables that need to be "
    ++"renamed."
  let newFV = getFreeVariables term2
  assertInternal (initFV == newFV)
    "Renaming bound variables should not change free variables"
  return term2
  where
    runRenameNeeded :: (Log.MonadLogger m, MonadError String m, HasCallStack) =>
                        T.Term -> Set.Set String -> m T.Term
    runRenameNeeded term1 forbidden = do
      checkBoundVariablesDistinct term1
      (flip evalStateT) Map.empty
        $(flip runReaderT) forbidden
          $ renameNeededMonadic term1

renameNeededMonadic :: (MonadState (Map.Map String String) m,
                          MonadReader (Set.Set String) m,
                          Log.MonadLogger m, MonadError String m,
                          HasCallStack) =>
                    T.Term -> m T.Term
renameNeededMonadic = \case
  T.TVar var -> do
    var' <- toCorrectMentionedVar var
    return $ T.TVar var
  T.TNum integer -> return $ T.TNum integer
  T.TLam var term -> do
    var' <- toCorrectBoundVar var
    term' <- renameNeededMonadic term
    return $ T.TLam var' term
  T.THole -> return $ T.THole
  T.TLet letBindings1 mainTerm1 -> do
    let (bindingVars1, sWeights1, hWeights1, boundTerms1) = unzip4 letBindings1
    bindingVars2 <- mapM toCorrectBoundVar bindingVars1
    boundTerms2 <- mapM renameNeededMonadic boundTerms1
    mainTerm2 <- renameNeededMonadic mainTerm1
    let letBindings2 = zip4 bindingVars2 sWeights1 hWeights1 boundTerms2
    return $ T.TLet letBindings2 mainTerm2
  T.TDummyBinds varSet1 term1 -> do
    let varList1 = Set.toList varSet1
    varList2 <- mapM toCorrectMentionedVar varList1
    let varSet2 = Set.fromList varList2
    term2 <- renameNeededMonadic term1
    return $ T.TDummyBinds varSet2 term2
  T.TRedWeight rw1 red1 -> do
    red2 <- case red1 of
              T.RApp term1 var1 -> do
                var2 <- toCorrectMentionedVar var1
                term2 <- renameNeededMonadic term1
                return $ T.RApp term2 var2
              T.RPlusWeight t1 rw2 t2 -> do
                t1' <- renameNeededMonadic t1
                t2' <- renameNeededMonadic t2
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
                      Log.MonadLogger m, MonadError String m,
                      HasCallStack)
                      => String -> m String
toCorrectBoundVar oldName = do
  forbiddenNames <- ask
  if (oldName `Set.member` forbiddenNames)
    then do
      newName <- freshName oldName forbiddenNames
      renameMap <- get
      assertInternal (oldName `Map.notMember` renameMap)
        "Old names should not be renamed twice, since binders are unique"
      let renameMap' = Map.insert oldName newName renameMap
      put renameMap'
      return newName
    else return oldName

-- | Given a variable name v and a set of forbidden names S, returns a new
-- variable name v' that is similar to v, but not in S.
--
-- Throws an error if v is not in S, i.e. if the renaming is not needed.
--
-- TODO: might be more user friendly to add an increasing index at the end of
-- the name. For now, I'll just get a fresh letter from the alphabet.
freshName :: (Log.MonadLogger m, MonadError String m, HasCallStack) =>
             String -> Set.Set String -> m String
freshName name forbiddenNames = do
  assertInternal (Set.member name forbiddenNames) $ "Renaming was "
    ++"attempted, but not needed. "++name++" is not in "++show forbiddenNames
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

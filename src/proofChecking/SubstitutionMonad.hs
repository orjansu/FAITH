{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | A monad with the invariant that all terms that you get out of the
-- substitutionMonad are properly renamed so that their bound variables
-- are distinct from the other bound variables from terms that are
-- previously gotten out of the monad and the initial set of forbidden
-- names.
--
-- The previous implementation relied on the false assumption that variables do
-- not need to be renamed the first time. This is not true. A counterexample is
-- (M + M + N)[(\a.a)/M][(\b.b)/N]
-- because the second M will be renamed to \b.b
--
-- The current implementetation relies on renaming all variables that need to
-- be renamed before letting them out of the monad, using renameNeeded.
module SubstitutionMonad (runSubstM
                         , getSubstitute
                         , applyContext
                         , getCtxFreeVars
                         , isFresh
                         , liftCheckM
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
import Data.List (zip4, unzip4, intersperse)
import Data.Foldable (foldlM)

import qualified MiniTypedAST as T
import ShowTypedTerm (showTypedTerm)
import TermCorrectness (getBoundVariables, numHoles, getFreeVariables
                       , checkBoundVariablesDistinct, getAllVariables)
import OtherUtils (applyAndRebuildM)
import ToLocallyNameless (toLocallyNameless)
import TermUtils (showSubstitute)

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
  checkSubstBVDistinct substSimpleMap initForbiddenNames
  let substMap = prepareSubstitutions substSimpleMap
      initSt = MkSubstSt {substitutions = substMap
                         , forbiddenNames = initForbiddenNames}
  (a, finalState) <- (flip runStateT) initSt $ getSubstM $ monadic
  let finalForbiddenNames = forbiddenNames finalState
  assertInternal (initForbiddenNames `Set.isSubsetOf` finalForbiddenNames)
    "Substitution map should only accumulate forbidden names."
  return (a, finalForbiddenNames)

-- | Checks that none of the substitutions has a bound variable that
-- has a name that is forbidden (in the forbidden names) or that one bound
-- variable in one substitution has the same name as a bound variable in
-- another substitution.
checkSubstBVDistinct :: HasCallStack =>
                        T.Substitutions -> Set.Set String -> CheckM [()]
checkSubstBVDistinct substitutions forbiddenNames = do
  Log.logInfoN . pack $ "Checking that the names of the bound variables in the "
    ++"substitutions are valid (i.e. distinct from each other and the free "
    ++"variables)."
  (flip evalStateT) forbiddenNames $
    mapM checkBVSubstitution $ Map.assocs substitutions
  where
    checkBVSubstitution :: HasCallStack =>
                           (String, T.Substitute)
                           -> StateT (Set.Set String) CheckM ()
    checkBVSubstitution (name, substitute) = do
      Log.logInfoN . pack $ "Checking substitute "++name++"="
        ++showSubstitute substitute
      case substitute of
        T.SLetBindings letBindings -> do
          let (bindVars, _sw, _hw, terms) = unzip4 letBindings
          checkBSSubstListBvsTerms bindVars terms
        T.SValue term -> checkBVTerm term
        T.SContext term -> checkBVTerm term
        T.SIntegerVar intExpr -> return ()
        T.SVar string -> return ()
        T.SVarSet varSet -> return ()
        T.SVarVect varVect -> return ()
        T.SValueContext term -> checkBVTerm term
        T.STerm term -> checkBVTerm term
        T.STerms terms -> mapM checkBVTerm terms >> return ()
        T.SPatterns ptns -> return ()
        T.SCaseStms stms -> do
          let (_, bindVars, terms) = unzip3 stms
          checkBSSubstListBvsTerms (concat bindVars) terms
        T.SConstructorName str -> return ()
        T.SReduction red -> case red of
          T.RApp T.THole var -> return ()
          T.RCase T.THole stms -> do
            let (_, bindVars, terms) = unzip3 stms
            checkBSSubstListBvsTerms (concat bindVars) terms
          T.RPlusWeight T.THole rw term -> checkBVTerm term
          T.RAddConst _i T.THole -> return ()
          T.RIsZero T.THole -> return ()
          T.RSeq T.THole term -> checkBVTerm term
          _ -> internalException $ "the non-reduction-context "
            ++showTypedTerm (T.TRedWeight 1 red)++" got all the way to"
            ++"substitution."

    checkBSSubstListBvsTerms bindVars terms = do
      let innerBVs = map getBoundVariables terms
          bindVarSet = Set.fromList bindVars
      forbiddenNames1 <- get
      let shouldBeDistinct = forbiddenNames1:bindVarSet:innerBVs
      forbiddenNames2 <- assertDisjointAndMerge shouldBeDistinct
      put forbiddenNames2

    checkBVTerm :: HasCallStack => T.Term -> StateT (Set.Set String) CheckM ()
    checkBVTerm term = do
      let bvSet = getBoundVariables term
      forbiddenNames1 <- get
      forbiddenNames2 <- assertDisjointAndMerge [bvSet, forbiddenNames1]
      put forbiddenNames2

    -- | asserts that every set in the list is disjoint from all other sets in
    -- the list.
    assertDisjointAndMerge :: (MonadError String m, Log.MonadLogger m,
                              HasCallStack, Ord a, Show a) =>
                      [Set.Set a] -> m (Set.Set a)
    assertDisjointAndMerge sets = do
      foldlM assertMerge2 Set.empty sets
      where
        assertMerge2 :: (MonadError String m, Log.MonadLogger m,
                               HasCallStack, Ord a, Show a) =>
                               Set.Set a -> Set.Set a -> m (Set.Set a)
        assertMerge2 set1 set2 = do
          assert (set1 `Set.disjoint` set2) $ "The variable(s) "
            ++show (set1 `Set.intersection` set2)++" should not be used in "
            ++"multiple bindings and should be distinct from the free "
            ++"variables."
          return $ set1 `Set.union` set2


-- | Checks whether the variable or variable vector corresponding to the
-- metavariable provided is among the
-- free or bound variables of the terms and other things that are substituted,
-- except for the variable(s) itself (themselves).
-- NOTE: the correctness of this check
-- depends on that all the fresh variables are added to the set of forbidden
-- names before substitution into the law term (see the use of
-- getFreshVariables in applySubstitution) and that all substitutions are
-- provided (see check in the typechecker).
isFresh :: HasCallStack => String -> SubstM Bool
isFresh metaVar = do
  xs <- getFreshCheckSet
  substMap <- gets substitutions
  let substWithoutMV = Map.delete metaVar substMap
  return $ all (xs `areFreshWrt` ) $ map fst $ Map.elems substWithoutMV
  where
    getFreshCheckSet = do
      substitute <- getSubstitute metaVar
      case substitute of
        T.SVar x -> return $ Set.singleton x
        T.SVarVect xs -> return $ Set.fromList xs
        _ -> internalException $ metaVar++" does not correspond to a variable "
              ++"or a variable list"

    areFreshWrt xs (T.SLetBindings letBindings) =
      let dummy = T.TLet letBindings (T.TNum 1)
      in xs `Set.disjoint` getAllVariables dummy
    areFreshWrt xs (T.SValue term) = xs `Set.disjoint` getAllVariables term
    areFreshWrt xs (T.SContext term) = xs `Set.disjoint` getAllVariables term
    areFreshWrt xs (T.SIntegerVar _) = True
    areFreshWrt xs (T.SVar var) = var `Set.notMember` xs
    areFreshWrt xs (T.SVarVect ys) = xs `Set.disjoint` Set.fromList ys
    areFreshWrt xs (T.SValueContext term) =
      xs `Set.disjoint` getAllVariables term
    areFreshWrt xs (T.SReduction red) =
      let dummy = T.TRedWeight 1 red
      in xs `Set.disjoint` getAllVariables dummy
    areFreshWrt xs (T.SVarSet varSet) = xs `Set.disjoint` varSet
    areFreshWrt xs (T.STerm term) = xs `Set.disjoint` getAllVariables term
    areFreshWrt xs (T.STerms terms) =
      all (\t -> xs `Set.disjoint` getAllVariables t) terms
    areFreshWrt xs (T.SPatterns patterns) =
      let (constructors, args) = unzip patterns
          argSet = Set.fromList $ concat args
      in xs `Set.disjoint` argSet
    areFreshWrt xs (T.SCaseStms branches) =
      let dummy = T.TRedWeight 1 (T.RCase (T.TNum 1) branches)
      in xs `Set.disjoint` getAllVariables dummy
    areFreshWrt xs (T.SConstructorName _) = True

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
          letBindings2 <- mapM renameLB letBindings1
          return $ T.SLetBindings letBindings2
          where
            renameLB (name1, sw1, hw1, term1) = do
              term2 <- prepareTermForSubstitution term1
              return (name1, sw1, hw1, term2)
        T.SValue term -> do
          prepared <- prepareTermForSubstitution term
          return $ T.SValue prepared
        T.SContext ctx -> contextUsed
        T.SIntegerVar intExpr -> return subst
        T.SVar string -> return subst
        T.SVarVect vars -> return subst
        T.SValueContext _ -> contextUsed
        T.SReduction _ -> contextUsed
        T.SVarSet varSet -> return subst
        T.STerm term -> do
          prepared <- prepareTermForSubstitution term
          return $ T.STerm prepared
        T.STerms terms -> do
          prepared <- mapM prepareTermForSubstitution terms
          return $ T.STerms prepared
        T.SPatterns ptns -> return subst
        T.SCaseStms caseStms1 -> do
          let dummy1 = T.TRedWeight 1 $ T.RCase (T.TNum 1) caseStms1
          dummy2 <- prepareTermForSubstitution dummy1
          T.TRedWeight 1 (T.RCase (T.TNum 1) caseStms2) <- return dummy2
          return $ T.SCaseStms caseStms2
        T.SConstructorName name -> return subst
    Nothing -> internalException $ "Substitution for "++metaVar++" not found"
  where
    contextUsed = internalException $  "use applyContext or "
                  ++"getContextFreeVars, not getSubstitute for contexts"

prepareTermForSubstitution :: HasCallStack => T.Term -> SubstM T.Term
prepareTermForSubstitution term = do
  res <- renameNeeded term
  addBVToForbiddenNames res
  return res

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

-- | since you can't get the contexts out via getSubstitute, this is a special
-- function to just get the free variables from it.
getCtxFreeVars :: String -> SubstM (Set.Set String)
getCtxFreeVars mv = do
  substMap <- gets substitutions
  case Map.lookup mv substMap of
    Just (T.SContext ctx,_) -> return $ getFreeVariables ctx
    Just (T.SReduction red,_) -> return $ getFreeVariables $ T.TRedWeight 1 red
    Just (T.SValueContext vctx,_) -> return $ getFreeVariables vctx
    Just _ -> internalException "getCtxFreeVars used for a non-context"
    Nothing -> internalException $ "substitute for "++mv++" not found."

-- | given a name corresponding to a context C and a term M, returns C[M],
-- properly renamed.
applyContext :: HasCallStack => String -> SubstM T.Term -> SubstM T.Term
applyContext ctxName termInstruction = do
  substMap <- gets substitutions
  (ctx, isUsed) <- getUniformContext ctxName substMap
  addBVToForbiddenNames ctx
  term <- termInstruction
  assertInternal (numHoles term == 0)
    "You may not insert a context into a context"
  appliedOldNames <- applyContext1 ctx term
  renameNeeded appliedOldNames
  where
    getUniformContext ctxName substMap = case Map.lookup ctxName substMap of
      Just (T.SContext ctx, isUsed) -> return (ctx, isUsed)
      Just (T.SValueContext ctx, isUsed) -> return (ctx, isUsed)
      Just (T.SReduction red, isUsed) -> return (T.TRedWeight 1 red, isUsed)
      _ -> internalException $ "no context substitution for "++ctxName
    applyContext1 :: HasCallStack => T.Term -> T.Term -> SubstM T.Term
    applyContext1 ctx term = do
      let holeSubstitution = Map.singleton dummy (T.STerm term, False)
          termBV = getBoundVariables term
      forbiddenNames1 <- gets forbiddenNames
      assertInternal (termBV `Set.isSubsetOf` forbiddenNames1)
        $ "The term to be inserted to a context should have added its bound "
        ++"variables to the set of forbidden names."
        ++show termBV++" should be a subset of "++show forbiddenNames1
      oldSubstitutions <- gets substitutions
      modify (\st -> st{substitutions = holeSubstitution})

      appliedCtx <- applyContext2 ctx

      modify  (\st -> st{substitutions = oldSubstitutions})
      forbiddenNames2 <- gets forbiddenNames
      return appliedCtx

    dummy :: String
    dummy = ""

    applyContext2 :: HasCallStack => T.Term -> SubstM T.Term
    applyContext2 = \case
      T.THole -> do
        T.STerm substTerm <- getSubstitute dummy
        return substTerm
      recursiveTerm -> applyAndRebuildM applyContext2 recursiveTerm

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
      (initLNL, initFV) = toLocallyNameless term1
  forbiddenNames1 <- gets forbiddenNames
  let shouldBeUnchanged = initBV Set.\\ forbiddenNames1

  term2 <- runRenameNeeded term1

  Log.logInfoN . pack $ "Checking correctness of renaming "
    ++showTypedTerm term1++" to "++showTypedTerm term2
  let newBV = getBoundVariables term2
      expectedForbiddenNames2 = newBV `Set.union` forbiddenNames1
  forbiddenNames2 <- gets forbiddenNames
  assertInternal (forbiddenNames2 == expectedForbiddenNames2) $
    "expected forbiddenNames ="++show expectedForbiddenNames2++
    "=="++show forbiddenNames2
  let unchanged = newBV Set.\\ forbiddenNames2
  assertInternal (unchanged == shouldBeUnchanged) $
    "Renaming just needed variables should not rename variables that do not "
    ++"need to be renamed. "++show unchanged++" /= "++show shouldBeUnchanged
  assertInternal (newBV `Set.disjoint` forbiddenNames1) $
    "Renaming needed variables should rename all variables that need to be "
    ++"renamed."
  let (newLNL, newFV) = toLocallyNameless term2
  assertInternal (initFV == newFV)
    "Renaming bound variables should not change free variables"
  assertInternal (initLNL == newLNL)
    "If M renames its bound variables to N, M should be alpha equivalent to N."
  return term2
  where
    runRenameNeeded :: HasCallStack =>
                        T.Term -> SubstM T.Term
    runRenameNeeded term1 = do
      checkBoundVariablesDistinct term1
      runRenameM $ renameNeededMonadic term1

data RenameSt = MkRenameSt
 { renamings :: Map.Map String String
     -- This is the map describing renamings that should take place.
 , forbiddenNames' :: Set.Set String
     -- These are the names that, if found in a term, that name should be
     -- changed to another name.
 , unchangedNames :: Set.Set String
     -- These are the names that should not be renamed to a new name if found
     -- in a term, but any new name should not be distinct from unchangedNames.
 }

newtype RenameM a = MkRenameM {getRenameM :: StateT RenameSt CheckM a}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String
           , MonadState RenameSt)

runRenameM :: RenameM a -> SubstM a
runRenameM monadic = do
  forbiddenNames1 <- gets forbiddenNames
  let initSt = (MkRenameSt {renamings = Map.empty
                           , forbiddenNames' = forbiddenNames1})
  (res, finalState) <- liftCheckM $
                          (flip runStateT) initSt
                            $ getRenameM monadic
  let forbiddenNames2 = forbiddenNames' finalState
  modify (\st -> st{forbiddenNames = forbiddenNames2})
  return res

renameNeededMonadic :: (HasCallStack) =>
                    T.Term -> RenameM T.Term
renameNeededMonadic = \case
  T.TNonTerminating -> return T.TNonTerminating
  T.TVar var1 -> do
    var2 <- toCorrectMentionedVar var1
    return $ T.TVar var2
  T.TNum integer -> return $ T.TNum integer
  T.TConstructor name vars1 -> do
    vars2 <- mapM toCorrectMentionedVar vars1
    return $ T.TConstructor name vars2
  T.TLam var1 term1 -> do
    var2 <- toCorrectBoundVar var1
    term2 <- renameNeededMonadic term1
    return $ T.TLam var2 term2
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
  T.TStackSpikes sw term1 -> do
    term2 <- renameNeededMonadic term1
    return $ T.TStackSpikes sw term2
  T.THeapSpikes hw term1 -> do
    term2 <- renameNeededMonadic term1
    return $ T.THeapSpikes hw term2
  T.TRedWeight rw1 red1 -> do
    red2 <- case red1 of
              T.RApp term1 var1 -> do
                var2 <- toCorrectMentionedVar var1
                term2 <- renameNeededMonadic term1
                return $ T.RApp term2 var2
              T.RCase decideTerm1 branches1 -> do
                decideTerm2 <- renameNeededMonadic decideTerm1
                let (cnames1, args1, terms1) = unzip3 branches1
                args2 <- mapM (mapM toCorrectBoundVar) args1
                terms2 <- mapM renameNeededMonadic terms1
                let branches2 = zip3 cnames1 args2 terms2
                return $ T.RCase decideTerm2 branches2
              T.RPlusWeight t1 rw2 t2 -> do
                t1' <- renameNeededMonadic t1
                t2' <- renameNeededMonadic t2
                return $ T.RPlusWeight t1' rw2 t2'
              T.RAddConst integer term1 -> do
                term2 <- renameNeededMonadic term1
                return $ T.RAddConst integer term2
              T.RIsZero term1 -> do
                term2 <- renameNeededMonadic term1
                return $ T.RIsZero term2
              T.RSeq term1 term2 -> do
                term1' <- renameNeededMonadic term1
                term2' <- renameNeededMonadic term2
                return $ T.RSeq term1' term2'
    return $ T.TRedWeight rw1 red2

toCorrectMentionedVar :: String -> RenameM String
toCorrectMentionedVar var = do
  renameMap <- gets renamings
  case Map.lookup var renameMap of
    Just newName -> return newName
    Nothing -> return var

toCorrectBoundVar :: HasCallStack
                      => String -> RenameM String
toCorrectBoundVar oldName = do
  forbiddenNames1 <- gets forbiddenNames'
  if (oldName `Set.member` forbiddenNames1)
    then do
      newName <- freshName oldName forbiddenNames1
      renameMap1 <- gets renamings
      assertInternal (oldName `Map.notMember` renameMap1)
        "Old names should not be renamed twice, since binders are unique"
      let renameMap2 = Map.insert oldName newName renameMap1
          forbiddenNames2 = Set.insert newName forbiddenNames1
      modify (\st -> st{renamings = renameMap2
                       , forbiddenNames' = forbiddenNames2})
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
    ++"attempted, but not needed. "++name++" should be in "++show forbiddenNames
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

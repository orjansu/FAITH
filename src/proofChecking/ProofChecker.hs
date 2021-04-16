{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module ProofChecker where

import qualified Control.Monad.Logger as Log
import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.Extra (andM)
import Control.Monad.State (StateT, runStateT, get, put, MonadState, State
                           , evalState, evalStateT, gets, modify)
import Data.Text (pack, Text)
import Data.Maybe (Maybe(Just, Nothing), catMaybes)
import Maybes (firstJusts)
import Data.List (permutations, intersperse)
import Data.List.Extra (firstJust)
import Data.Char (isDigit)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import qualified LanguageLogic as Lang
import qualified Common as Com (ImpRel(..))
import ToLocallyNameless (toLocallyNameless)
import qualified LocallyNameless as LNL
import ToPrettyLNL (showLNL)
import ShowTypedTerm (showTypedTerm)
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables)

newtype CheckM a = MkM {getM :: (ExceptT String
                                  (Log.WriterLoggingT Identity) a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String)

instance MonadFail CheckM where
  fail str = throwError str

-- | Checks whether a detailed proof script is correct. Returns a [String],
-- containing a log and error message if it is incorrect, and Nothing
-- if it is correct.
--
-- Assumes that the incoming proof script is typechecked.
checkDetailedProof :: T.ProofScript -> Maybe [String]
checkDetailedProof proofScript = runCheckM $ check proofScript

runCheckM :: CheckM () -> Maybe [String]
runCheckM monadComputation =
  let r = runIdentity $
            Log.runWriterLoggingT $
                runExceptT $
                  getM $
                    monadComputation
  in case r of
    (Right (), logs) -> Nothing
    (Left errorMsg, logs) -> Just $(map toLine logs) ++ [errorMsg]

toLine :: Log.LogLine -> String
toLine (loc, logsource, loglevel, logstr) =
  (show logstr)

class Checkable a where
  check :: a -> CheckM ()

instance Checkable T.ProofScript where
  check (T.DProofScript theorems) = mapM check theorems >> return ()

instance Checkable T.Theorem where
  check (T.DTheorem (T.DProposition freeVars start imprel goal) proof) = do
    checkProofSteps proof start imprel freeVars goal

type GlobalImpRel = Com.ImpRel
type Start = T.Term
type Goal = T.Term

checkProofSteps :: T.Proof
                   -> Start
                   -> GlobalImpRel
                   -> T.FreeVars
                   -> Goal
                   -> CheckM ()
checkProofSteps (T.Simple proofSteps) start globalImpRel freeVars goal = do
  let (T.PSMiddle startTerm _ _ _) = head proofSteps
  checkAlphaEquiv start startTerm
  mapM (checkStep globalImpRel freeVars) proofSteps
  let (T.PSMiddle _ _ _ endTerm) = last proofSteps
  checkAlphaEquiv goal endTerm

-- | Checks if a single step is valid. This computation may be run
-- independently in parallel for each step to speed things up if that is an
-- issue. Could maybe use the globally free variables to speed things up later.
checkStep :: GlobalImpRel -> T.FreeVars -> T.ProofStep -> CheckM ()
checkStep globalImpRel
          freeVars
          (T.PSMiddle term1 command localImpRel term2) = do
  Log.logInfoN . pack $ "checking that "++showTypedTerm term1++" "
  Log.logInfoN . pack $ show localImpRel
  Log.logInfoN . pack $ showTypedTerm term2
  Log.logInfoN . pack $ "using the law "++show command
  Log.logInfoN . pack $ "with the global improvement relation being "
    ++show globalImpRel
  assert (localImpRel `Lang.impRelImplies` globalImpRel)
    $ show localImpRel ++ " should imply "++ show globalImpRel
  case command of
    T.AlphaEquiv -> checkAlphaEquiv term1 term2
    T.Law context
          (Law.DLaw lawName lawLHS lawImpRel lawRHS)
          substitutions -> do
      assert (lawImpRel == localImpRel) "The improvement relation of the law must be the same as the improvement relation in the proof"
      subterm <- getSubterm context term1
      let contextVars = getAllVars context
      Log.logInfoN . pack $ "applying substitution from subterm to law"
      -- TODO log messages
      substToLHS <- applySubstitution lawLHS substitutions contextVars
      checkRuleAlphaEquiv lawLHS subterm substToLHS
      substToRHS <- applySubstitution lawLHS substitutions contextVars
      fvOrig <- getFreeVars subterm
      fvTransformed <- getFreeVars substToRHS
      assert (fvOrig == fvTransformed) "The transformation should not make bound variables free."
      rhsTerm <- applyContext context substToRHS

      -- This shows that we could generate the next term ourselves instead.
      -- However, it is more important to typecheck rhsTerm if we generate it.
      checkRuleAlphaEquiv lawRHS rhsTerm term2

      -- This check below should not be needed. Quickcheck it later and maybe
      -- remove if it impedes performance.
      Log.logInfoN . pack $ "Checking that the resulting term of the transformation typechecks."
      typeCheck rhsTerm freeVars
      return undefined

-- | given C and M, returns N such that C[N] =alpha= M
-- For now, this is the version that I implement:
-- C needs to be a syntactic copy of M, with exactly one of its subterms
-- replaced with a hole. For possible variations, see typecheckerNotes.
getSubterm :: T.Term -> T.Term -> CheckM T.Term
getSubterm context term = do
  Log.logInfoN $ pack $ "matching C="++showTypedTerm context
    ++" on M="++showTypedTerm term++" to get the subterm"
  assertInternal (numHoles context == 1) $ "Only a single hole in C is "
    ++"currently supported"
  assertInternal (numHoles term == 0) $ "M must not be a context"
  returnPotentialTerm $ getSubterm' context term
  where
    getSubterm' :: T.Term -> T.Term -> Maybe T.Term
    getSubterm' (T.TVar _) _ = Nothing
    getSubterm' (T.TNum _) _ = Nothing
    getSubterm' (T.TLam v1 t1) (T.TLam v2 t2)
      | v1 == v2 = getSubterm' t1 t2
    getSubterm' T.THole term = Just term
    getSubterm' (T.TLet lbs1 term1) (T.TLet lbs2 term2) =
      if lbs1 == lbs2
        then getSubterm' term1 term2
        else firstJust matchBinding $ zip lbs1 lbs2
      where
        matchBinding ((v1, sw1, hw1, t1), (v2, sw2, hw2, t2))
          | v1 == v2 && sw1 == sw2 && hw1 == hw2 = getSubterm' t1 t2
          | otherwise = Nothing
    getSubterm' (T.TDummyBinds vs1 t1) (T.TDummyBinds vs2 t2)
      | vs1 == vs2 = getSubterm' t1 t2
    getSubterm' (T.TRedWeight rw1 red1) (T.TRedWeight rw2 red2)
      | rw1 == rw2 = case (red1, red2) of
        (T.RApp t1 v1, T.RApp t2 v2) | v1 == v2 -> getSubterm' t1 t2
        (T.RPlusWeight t11 rw1 t12, T.RPlusWeight t21 rw2 t22)
          | rw1 == rw2 -> firstJusts [getSubterm' t11 t21, getSubterm' t21 t22]
        (_, _) -> Nothing
    getSubterm' _ _ = Nothing

    returnPotentialTerm :: Maybe T.Term -> CheckM T.Term
    returnPotentialTerm Nothing = fail contextDoesNotMatch
    returnPotentialTerm (Just term) = return term

    contextDoesNotMatch :: String
    contextDoesNotMatch = "C does not match M."

-- | Given the subtermterm M and the whole term N, this function returns the
-- context C such that C[M] = N. This equivalence is strict equivalence and not
-- alpha equivalence.
--
-- Fails if M is not a subterm of N
-- TODO think about the case if there are more than one hole
-- TODO This failed because you might get to the case where the subterm is
-- present in more than one place in the term. Instead, you will need to
-- specify the context instead, and use this getContext in the typechecker.
{-
getContext :: T.Term -> T.Term -> CheckM T.Term
getContext term1 term2 = do
  Log.logInfoN $ pack $ "Checking if M is a subterm of N, i.e. if there is a "
    ++"C such that C[M] = N"
  Log.logInfoN $ pack $ "| where M = "++showTypedTerm term1
  Log.logInfoN $ pack $ "| and N = "++showTypedTerm term2
  case getContext' term1 term2 of
    Just context -> return context
    Nothing -> fail notSubTerm
  where
    -- | given M and N, returns C such that C[M] = N
    getContext' :: T.Term -> T.Term -> Maybe T.Term
    getContext' subterm term | subterm == term = return T.THole
    getContext' subterm (T.TVar _) = Nothing
    getContext' subterm (T.TNum _) = Nothing
    getContext' subterm (T.TLam var term)
      | subterm == term = return (T.TLam var T.THole)
      | isJust subMatch = let Just ctx = subMatch
                          in return $ T.TLam var ctx
      where subMatch = getContext' subterm term
    getContext' subterm T.THole = Nothing --This should not happen.
    getContext' subterm (T.TLet letBindings term)
      | subterm == term = return (T.TLet letBindings T.THole)
      where
        matchLetBindings subterm [] = Nothing

        matchLetBinding (var, sw, hw, term) | subterm == term = T.THole

    notSubTerm :: String
    notSubTerm = "| M is not a subterm of N."
-}

-- | Given C and M, where C is a context and M is a term, returns C[M].
-- TODO Currently only supports contexts with a single hole
-- Note: This is kind of the same as applySubstitution.
applyContext :: T.Term -> T.Term -> CheckM T.Term
applyContext context insertTerm = do
  Log.logInfoN . pack $ "applying the context C="++showTypedTerm context
    ++ " to the term M="++showTypedTerm insertTerm
  assertInternal (numHoles context == 1) $"only insertion with a single hole"
    ++ "is currently supported."
  assertInternal (numHoles insertTerm == 0)$"the inserted term must not have "
    ++"any holes."
  assertInternal
    (getBoundVariables context `Set.disjoint` getBoundVariables insertTerm)
    $ "C and M must not have bound variables with the same name"
  return $ appCtx context
  where
    -- | applies the context by inserting insertTerm where there is a hole,
    -- and is the identity function if no context is applied
    appCtx (T.TVar var) = T.TVar var
    appCtx (T.TNum integer) = T.TNum integer
    appCtx (T.TLam var term) = T.TLam var $ appCtx term
    appCtx (T.THole) = insertTerm
    appCtx (T.TLet letBindings term) = let appLBS = map appLB letBindings
                                           appTerm = appCtx term
                                       in T.TLet appLBS appTerm
      where
        appLB (var, sw, hw, term) = (var, sw, hw, appCtx term)
    appCtx (T.TDummyBinds varSet term) = T.TDummyBinds varSet $ appCtx term
    appCtx (T.TRedWeight redWeight red) =
      let appRed = case red of
                     T.RApp term var -> T.RApp (appCtx term) var
                     T.RPlusWeight t1 rw t2 ->
                        T.RPlusWeight (appCtx t1) rw (appCtx t2)
      in T.TRedWeight redWeight appRed

-- | Returns the number of holes in a term or context
numHoles :: T.Term -> Integer
numHoles (T.TVar _var) = 0
numHoles (T.TNum _integer) = 0
numHoles (T.TLam _var term) = numHoles term
numHoles (T.THole) = 1
numHoles (T.TLet letBindings term) = numHoles term + numHolesInLBS
  where
    numHolesInLBS = sum $ map numHolesInLB letBindings
    numHolesInLB (_var, _sw, _hw, term) = numHoles term
numHoles (T.TDummyBinds _varSet term) = numHoles term
numHoles (T.TRedWeight _redWeight red) = case red of
  T.RApp term _var -> numHoles term
  T.RPlusWeight t1 _rw t2 -> numHoles t1 + numHoles t2

-- | Given a term, returns the set of all variable names used in that term,
-- regardless of if the variables are free or bound
getAllVars :: T.Term -> Set.Set String
getAllVars (T.TVar var) = Set.singleton var
getAllVars (T.TNum integer) = Set.empty
getAllVars (T.TLam var term) = Set.singleton var `Set.union` getAllVars term
getAllVars (T.THole) = Set.empty
getAllVars (T.TLet letBindings term) =
  getLBSVars letBindings `Set.union` getAllVars term
  where
    getLBSVars = Set.unions . map getLBVars
    getLBVars :: (String, T.StackWeight, T.HeapWeight, T.Term) -> Set.Set String
    getLBVars (name, _sw, _hw, term) = let termSet = getAllVars term
                                       in Set.insert name termSet
getAllVars (T.TDummyBinds varSet term) = varSet `Set.union` getAllVars term
getAllVars (T.TRedWeight _redWeight red) =
  case red of
    T.RApp term var -> let termSet = getAllVars term
                       in Set.insert var termSet
    T.RPlusWeight term1 _rw term2 ->
      getAllVars term1 `Set.union` getAllVars term2

type IsUsed = Bool
data SubstSt = MkSubstSt { substitutions :: Map.Map String (T.Term, IsUsed)
                         , forbiddenNames :: Set.Set String
                         }

newtype SubstM a = MkSubstM {getSubstM :: (StateT SubstSt CheckM a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String
           , MonadState SubstSt)
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
applySubstitution law substSimple initForbiddenNames = do
  Log.logInfoN . pack $ "applying substitution {"++showSubst++"}"
  Log.logInfoN . pack $ "to law term"++show law
  Log.logInfoN . pack $ "With forbidden names "++ show initForbiddenNames
  let toMapEntry = (\(name, term) -> (name, (term, False)))
      substSet = Set.map toMapEntry substSimple
      substAscList = Set.toAscList substSet
      substMap = Map.fromAscList substAscList
      initSt = MkSubstSt {substitutions = substMap
                         , forbiddenNames = initForbiddenNames}
  (flip evalStateT) initSt $ getSubstM $ substLawTerm law
  where
    showSubst = concat $
                 intersperse "," $
                   map showSingle $
                     Set.toList substSimple
    showSingle (name, term) = show name ++ " -> "++showTypedTerm term

    substLawTerm :: Law.Term -> SubstM T.Term
    substLawTerm lawTerm = case lawTerm of
      Law.TValueMetaVar valueMV -> do
        substitutableTerm <- getSubstTerm valueMV
        checkIsValue substitutableTerm
        return substitutableTerm
      Law.TAppCtx ctxMV term -> undefined
      Law.TLet letBindings term -> undefined
      Law.TDummyBinds varSet term -> undefined

    checkIsValue :: (MonadError String m) => T.Term -> m ()
    checkIsValue term = assert (isValue term)
      $ "M should be a value. M="++showTypedTerm term
      where
        isValue (T.TVar _var) = False
        isValue (T.TNum _integer) = True
        isValue (T.TLam _var _term) = True
        isValue (T.THole) = False
        isValue (T.TLet _letBindings _term) = False
        isValue (T.TDummyBinds _varSet term) = isValue term
        isValue (T.TRedWeight _redWeight _redFD) = False

    getSubstTerm :: String -> SubstM T.Term
    getSubstTerm metaVar = do
      substMap <- gets substitutions
      case Map.lookup metaVar substMap of
        Just (term, isUsed) ->
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
              let forbidden' = termBV `Set.union` forbidden
                  setToUsed = (\(t, False) -> (t, True))
                  substMap' = Map.adjust setToUsed metaVar substMap
              modify (\st -> st{forbiddenNames = forbidden'
                               , substitutions = substMap'})
              return term
        Nothing -> throwError $ "Substitution for "++metaVar++" not found"

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

-- | Finds the names of the free variables of the term
getFreeVars :: T.Term -> CheckM (Set.Set String)
getFreeVars term = do
  (_lnlTerm, freeVars) <- runToLocallyNameless term
  return freeVars

-- | Checks whether the term type-checks, i.e. if all variables are bound or
-- declared free.
--
-- Status: one way is tp unpype it and run it through the normal typechecker.
-- It is ineffective, but it relies on the single implementation of
-- typechecking. A better approach might be to divide the typechecker into one
-- phase that converts and one that typechecks. TODO typechecker needs more
-- context to be able to typecheck a term instead of the whole program
typeCheck :: T.Term -> T.FreeVars -> CheckM ()
typeCheck = undefined

class AlphaEq a where
  isAlphaEquiv :: a -> a -> CheckM Bool
  checkAlphaEquiv :: a -> a -> CheckM ()

instance AlphaEq T.Term where
  checkAlphaEquiv :: T.Term -> T.Term -> CheckM ()
  checkAlphaEquiv term1 term2 = do
    Log.logInfoN . pack $ "Checking that M and N are alpha equivalent"
    Log.logInfoN . pack $ "| where M = "++showTypedTerm term1
    Log.logInfoN . pack $ "| and N = "++showTypedTerm term2
    Log.logInfoN . pack $ "| see debug output for details."
    alphaEq <- isAlphaEquiv term1 term2
    assert alphaEq $ "| The locally-nameless representation "
      ++"of M and N should be equal"

  isAlphaEquiv :: T.Term -> T.Term -> CheckM Bool
  isAlphaEquiv term1 term2 | term1 == term2 = return True
                           | otherwise = do
    Log.logDebugN . pack $ "Determining wheter M and N are alpha equivalent,"
    Log.logDebugN . pack $ "| where M = "++ showTypedTerm term1
    Log.logDebugN . pack $ "| and N = "++showTypedTerm term2
    (lnlTerm1, _) <- runToLocallyNameless term1
    (lnlTerm2, _) <- runToLocallyNameless term2
    Log.logDebugN . pack $ "| Locally nameless representation of M is  "
      ++showLNL lnlTerm1
    Log.logDebugN . pack $ "| Locally nameless representation of N is "
      ++ showLNL lnlTerm2
    return (lnlTerm1 == lnlTerm2)

instance AlphaEq T.LetBindings where
  checkAlphaEquiv lbs1 lbs2 = do
    bindingsAlphaEq <- isAlphaEquiv lbs1 lbs2
    case bindingsAlphaEq of
      True -> return ()
      False -> do
        Log.logDebugN . pack $ "first let-binding is "
          ++showTypedTerm (T.TLet lbs1 T.THole)
        Log.logDebugN . pack $ "second let-binding is"
          ++showTypedTerm (T.TLet lbs2 T.THole)
        fail "let bindings not alpha equivalent"
  -- | given { x1 = M1 ... xn = Mn} and { y1 = N1 ... yn = Nn }
  -- returns whether forall i . xi and yi have the same canonical name
  -- and forall i . Mi =alpha= Ni
  --
  -- That is, it does care about order and the names of variables.
  -- The weights should also be the same.
  isAlphaEquiv lbs1 lbs2 = let pairs = zip lbs1 lbs2
                           in andM $ map checkEq pairs
    where
      checkEq :: ((String, Integer, Integer, T.Term)
                , (String, Integer, Integer, T.Term))
                -> CheckM Bool
      checkEq ((n1, sw1, hw1, t1), (n2, sw2, hw2, t2))
        | n1 == n2 && sw1 == sw2 && hw1 == hw2 = isAlphaEquiv t1 t2
        | otherwise = return False

-- | Given the law term L and two terms M and N,
-- this function checks alpha equivalance of M and N. If L contains let-terms
-- this function checks if M and N are equal with respect to alpha renaming and
-- reordering of let:s.
--
-- Currently, the implementation is very inefficient. It checks all
-- permutations of all let:s. Because of laziness, there are some computations
-- that are saved. Some things may also easily be paralellizable.
--
-- Subfunctions may be moved to base level
checkRuleAlphaEquiv :: Law.Term -> T.Term -> T.Term -> CheckM ()
checkRuleAlphaEquiv lawTerm m n = do
  orderedEq <- isAlphaEquiv m n
  if orderedEq
    then return ()
    else if containsLet lawTerm
      then let permutations = getAllLetPermutations m
           in if any (isOrderedAlphaEq n) permutations
                then return ()
                else fail "Not alpha equivalent, even with reordering of let:s"
      else fail "Not alpha equivalent, and law term does not contain let."
  where
    containsLet :: Law.Term -> Bool
    containsLet (Law.TValueMetaVar _) = False
    containsLet (Law.TAppCtx mv term) = containsLet term
    containsLet (Law.TLet _ _) = True
    containsLet (Law.TDummyBinds _ term) = containsLet term

    getAllLetPermutations :: T.Term -> [T.Term]
    getAllLetPermutations term = case term of
      (T.TVar var) -> [T.TVar var]
      (T.TNum i) -> [T.TNum i]
      (T.TLam var term) -> recursePerms term (T.TLam var)
      (T.THole) -> [T.THole]
      (T.TLet letBindings term) ->
        let permsLB = permutations letBindings
            permsTerm = getAllLetPermutations term
            combinedPerms = [(lbs, term) | lbs <- permsLB, term <- permsTerm]
            toLetBindings = (\(lbs, term) -> T.TLet lbs term)
        in map toLetBindings combinedPerms
      (T.TDummyBinds varSet term) -> recursePerms term (T.TDummyBinds varSet)
      (T.TRedWeight rw1 red) -> case red of
        T.RApp term var ->
          recursePerms term (\t -> T.TRedWeight rw1 (T.RApp t var))
        T.RPlusWeight term1 rw2 term2 ->
          let perms1 = getAllLetPermutations term1
              perms2 = getAllLetPermutations term2
              combinedPerms = [(t1, t2) | t1 <- perms1, t2 <- perms2]
              toPlus = \(t1, t2) -> T.TRedWeight rw1 (T.RPlusWeight t1 rw2 t2)
          in map toPlus combinedPerms

    recursePerms recurseTerm wrapTerm =
      let perms = getAllLetPermutations recurseTerm
      in map wrapTerm perms

    isOrderedAlphaEq :: T.Term -> T.Term -> Bool
    isOrderedAlphaEq m n = let (mLNL, _) = toLocallyNameless m
                               (nLNL, _) = toLocallyNameless n
                           in mLNL == nLNL


runToLocallyNameless :: T.Term -> CheckM (LNL.Term, Set.Set String)
runToLocallyNameless term = return $ toLocallyNameless term

liftEither :: Either String a -> CheckM a
liftEither (Left errorMsg) = throwError errorMsg
liftEither (Right a) = return a

assert :: (MonadError String m) => Bool -> String -> m ()
assert True _ = return ()
assert False description = throwError $ "assertion failed: "++description

assertInternal :: (Log.MonadLogger m, MonadError String m) =>
                  Bool -> String -> m ()
assertInternal True _ = return ()
assertInternal False description = do
  Log.logOtherN (Log.LevelOther (pack "InternalAssertion")) $ pack description
  throwError $ "Internal assertion failed: "++description

{-
matchLaw :: Law.Term -> T.Term -> [Map.Map String T.Term]
matchLaw (Law.TValueMetaVar mv) term = case term of
  T.TNum n -> [Map.singleton mv term]
  T.TLam v term -> [Map.singleton mv term]
  _ -> []
matchLaw (Law.TAppCtx mvC termPtn) term = undefined--findContextMatch termPtn term

-- | given a law term L and a term M, returns every C such that there is
-- a term N such that N matches L. In math:
-- L -> M -> [C1..Cn] st. forall i in (1..n). exists N s.t Ci[N] `matches` L
findContextMatch :: Law.Term -> T.Term -> [T.Term]
findContextMatch (Law.TValueMetaVar mv) term
  | isValue term = Just term
  | otherwise = recurse (findContextMatch (Law.TValueMetaVar mv)) term

-- | given f and M, apply f to all subterms one step down into M, and return
-- the list [N1...Nn] of all those subterms that returns Just Ni.
recurse :: (T.Term -> Maybe T.Term) -> T.Term -> [T.Term]
recurse f (T.TVar _) = []
recurse f (T.TNum _) = []
recurse f (T.TLam _ term) = catMaybes [f term]
recurse f (T.THole) = []
recurse f (T.TLet letBindings term) =
  let lbMaybeRecs = map recLB letBindings
  in catMaybes $ f term:lbMaybeRecs
  where
    recLB (_var, _sw, _hw, term) = f term
recurse f (T.TDummyBinds _ term) = catMaybes [f term]
recurse f (T.TRedWeight rw red) = case red of
  T.RApp term _var -> catMaybes [f term]
  T.RPlusWeight t1 _rw t2 -> catMaybes [f t1, f t2]


isValue :: T.Term -> Bool
isValue (T.TNum _) = True
isValue (T.TLam _ _) = True
isValue _ = False

data MatchAns = Yes | No | Recursion

matches :: Law.Term -> T.Term -> MatchAns
matches (Law.TValueMetaVar _) t = case t of
  T.TNum _ -> Yes
  T.TLam _ _ -> Yes
  _ -> No
matches (Law.TAppCtx _ _) t = Recursion
matches (Law.TLet _ _) t = Recursion
matches (Law.TDummyBinds _ _) t = Recursion
-}

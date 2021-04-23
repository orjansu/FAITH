{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module ProofChecker where

import qualified Control.Monad.Logger as Log
import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Extra (andM)

import Data.Text (pack, Text)
import Data.Maybe (Maybe(Just, Nothing), catMaybes)
import Maybes (firstJusts)
import Data.List (permutations, intersperse)
import Data.List.Extra (firstJust)
import Data.Char (isDigit)
import qualified Data.Set as Set

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law
import qualified LanguageLogic as Lang
import qualified Common as Com (ImpRel(..))
import ToLocallyNameless (toLocallyNameless)
import qualified LocallyNameless as LNL
import ToPrettyLNL (showLNL)
import ShowTypedTerm (showTypedTerm)
import TermCorrectness (checkBoundVariablesDistinct, getBoundVariables
                       , checkTypedTerm, numHoles, getFreeVariables)
import CheckMonad (CheckM, runCheckM, assert, assertInternal)
import OtherUtils (noSupport)
import Substitution (applySubstitution)

-- | Checks whether a detailed proof script is correct. Returns a [String],
-- containing a log and error message if it is incorrect, and Nothing
-- if it is correct.
--
-- Assumes that the incoming proof script is typechecked.
checkDetailedProof :: T.ProofScript -> Maybe [String]
checkDetailedProof proofScript =
  case runCheckM $ check proofScript of
    Right () -> Nothing
    Left errorMsgs -> Just errorMsgs

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
          (T.DFreeVars termFreeVars varFreeVars)
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
          (Law.DLaw lawName lawLHS lawImpRel lawRHS _sideCond)
          substitutions -> do
      assert (lawImpRel == localImpRel)
        $ "The improvement relation of the law must be the same as the "
        ++"improvement relation in the proof"
      -- This ^ shows that the localImpRel could be generated
      subterm <- getSubterm context term1
      let contextBV = getBoundVariables context
          forbiddenNames = contextBV `Set.union` varFreeVars
      Log.logInfoN . pack $ "applying substitution from subterm to law"
      -- TODO log messages
      substToLHS <- applySubstitution lawLHS substitutions forbiddenNames
      checkRuleAlphaEquiv lawLHS subterm substToLHS
      substToRHS <- applySubstitution lawLHS substitutions forbiddenNames
      let fvOrig = getFreeVariables subterm
          fvTransformed = getFreeVariables substToRHS
      assert (fvOrig == fvTransformed) $ "The transformation should not make"
        ++"bound variables free."
      rhsTerm <- applyContext context substToRHS
      -- This shows that we could generate the next term ourselves instead.
      -- However, it is more important to typecheck rhsTerm if we generate it.
      checkRuleAlphaEquiv lawRHS rhsTerm term2
      -- This check below should not be needed. Quickcheck it later and maybe
      -- remove if it impedes performance.
      Log.logInfoN . pack $ "Checking that the resulting term of the transformation typechecks."
      checkTypedTerm rhsTerm varFreeVars

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
    returnPotentialTerm Nothing = throwError contextDoesNotMatch
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
        throwError "let bindings not alpha equivalent"
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
                else throwError "Not alpha equivalent, even with reordering of let:s"
      else throwError "Not alpha equivalent, and law term does not contain let."
  where
    containsLet :: Law.Term -> Bool
    containsLet (Law.TValueMetaVar _) = False
    containsLet (Law.TVar _) = False
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

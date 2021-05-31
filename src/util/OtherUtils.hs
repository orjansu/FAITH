{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module OtherUtils ( applyAndRebuild
                  , applyAndRebuildM
                  , filterNoise
                  , applyOnLawSubterms
                  , applyOnLawSubtermsM
                  , applyOnSubterms
                  , applyOnSubtermsM
                  , distinct) where

import Control.Monad.Except (MonadError, throwError)
import Data.List (zip4, unzip4)
import qualified Control.Monad.Logger as Log
import Data.List.Extra (replace)
import Data.Maybe (catMaybes)
import qualified Data.Set as Set

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law

-- | given M and f, applies f to all subterms of M and then returns the changed
-- term. sort of like fmap.
applyAndRebuild :: T.Term -> (T.Term -> T.Term) -> T.Term
applyAndRebuild term f = case term of
  T.TNonTerminating -> term
  T.TVar _ -> term
  T.TNum _ -> term
  T.TConstructor _ _ -> term
  T.TLam var term -> T.TLam var (f term)
  T.THole -> term
  T.TLet letBindings term ->
    let (vars, sws, hws, terms) = unzip4 letBindings
        fTerms = map f terms
        fLetBindings = zip4 vars sws hws fTerms
        fTerm = f term
    in T.TLet fLetBindings fTerm
  T.TDummyBinds varSet term -> T.TDummyBinds varSet (f term)
  T.TStackSpikes stackWeight term -> T.TStackSpikes stackWeight (f term)
  T.THeapSpikes heapWeight term -> T.THeapSpikes heapWeight (f term)
  T.TRedWeight rw1 red -> T.TRedWeight rw1 fRed
    where
      fRed = case red of
        T.RApp term var -> T.RApp (f term) var
        T.RCase term stms -> let fTerm = f term
                                 (cnames, args, terms) = unzip3 stms
                                 fTerms = map f terms
                                 fStms = zip3 cnames args fTerms
                             in T.RCase fTerm fStms
        T.RPlusWeight term1 rw2 term2 -> T.RPlusWeight (f term1) rw2 (f term2)
        T.RAddConst integer term -> T.RAddConst integer (f term)
        T.RIsZero term -> T.RIsZero (f term)
        T.RSeq term1 term2 -> T.RSeq (f term1) (f term2)

-- | Given a monadic function on a term, applies it to all the subterms of a
-- term and reassembles the term after the monadic
-- computation has been applied to the subterms. Does not change terms that
-- do not contain subterms
applyAndRebuildM :: (Monad m, MonadFail m) =>
                    (T.Term -> m T.Term) -> T.Term -> m T.Term
applyAndRebuildM f bigTerm = case bigTerm of
  T.TNonTerminating -> return bigTerm
  T.TVar var -> return bigTerm
  T.TNum integer -> return bigTerm
  T.TConstructor _ _ -> return bigTerm
  T.TLam var subterm1 -> do
    subterm2 <- f subterm1
    return $ T.TLam var subterm2
  T.THole -> fail "Contains no subterms"
  T.TLet letBindings1 mainTerm1 -> do
    let (vars1, sWeights1, hWeights1, letTerms1) = unzip4 letBindings1
    letTerms2 <- mapM f letTerms1
    mainTerm2 <- f mainTerm1
    let letBindings2 = zip4 vars1 sWeights1 hWeights1 letTerms2
    return $ T.TLet letBindings2 mainTerm2
  T.TDummyBinds varSet1 term1 -> do
    term2 <- f term1
    return $ T.TDummyBinds varSet1 term2
  T.TStackSpikes sw term -> do
    fTerm <- f term
    return $ T.TStackSpikes sw fTerm
  T.THeapSpikes hw term -> do
    fTerm <- f term
    return $ T.THeapSpikes hw fTerm
  T.TRedWeight redWeight red1 -> do
    red2 <- case red1 of
              T.RApp term1 var -> do
                term2 <- f term1
                return $ T.RApp term2 var
              T.RCase dTerm cases -> do
                fdTerm <- f dTerm
                let (constructors, args, terms) = unzip3 cases
                fTerms <- mapM f terms
                let fCases = zip3 constructors args fTerms
                return $ T.RCase fdTerm fCases
              T.RPlusWeight subterm1 redWeight' subterm2 -> do
                subterm1' <- f subterm1
                subterm2' <- f subterm2
                return $ T.RPlusWeight subterm1' redWeight' subterm2'
              T.RAddConst int term -> do
                fTerm <- f term
                return $ T.RAddConst int fTerm
              T.RIsZero term -> do
                fTerm <- f term
                return $ T.RIsZero fTerm
              T.RSeq term1 term2 -> do
                fTerm1 <- f term1
                fTerm2 <- f term2
                return $ T.RSeq fTerm1 fTerm2
    return $ T.TRedWeight redWeight red2

filterNoise :: String -> String
filterNoise = let removeChars = filter (\c -> c /='\"' && c /= '\n')
                  lessWhiteSpace = replace "  " " "
              in lessWhiteSpace . removeChars

-- | designed to be used to cover all the simple recursive and base cases of
-- a function. Given the term, base value, recursive case and a combinator
-- function, the function returns the base value all terms that do not
-- contain subterms, and the recursive case to all subterms. It then combines
-- results if there are more than one using the combinator function, and then
-- returns the result.
applyOnSubterms :: T.Term
                  -> b
                  -> (T.Term -> b)
                  -> ([b] -> b)
                  -> b
applyOnSubterms bigTerm baseValue recurseFun combinator = case bigTerm of
  T.TNonTerminating -> baseValue
  T.TVar _ -> baseValue
  T.TNum _ -> baseValue
  T.TConstructor _ _ -> baseValue
  T.TLam _ term -> recurseFun term
  T.THole -> baseValue
  T.TLet letBindings mainTerm ->
    let (_, _, _, innerTerms) = unzip4 letBindings
    in combinator $ map recurseFun (mainTerm:innerTerms)
  T.TDummyBinds _ term -> recurseFun term
  T.TStackSpikes _ term -> recurseFun term
  T.THeapSpikes _ term -> recurseFun term
  T.TRedWeight _ red -> case red of
    T.RApp term _ -> recurseFun term
    T.RCase mainTerm caseStms ->
      let (_, _, innerTerms) = unzip3 caseStms
      in combinator $ map recurseFun (mainTerm:innerTerms)
    T.RPlusWeight term1 _ term2 ->
      combinator $ map recurseFun [term1, term2]
    T.RAddConst _ term -> recurseFun term
    T.RIsZero term -> recurseFun term
    T.RSeq term1 term2 -> combinator $ map recurseFun [term1, term2]

-- | same as applyOnSubterms, but for a monadic function.
applyOnSubtermsM :: (Monad m) =>
                     T.Term
                     -> b
                     -> (T.Term -> m b)
                     -> ([b] -> b)
                     -> m b
applyOnSubtermsM bigTerm baseValue recurseFun combinator = case bigTerm of
  T.TNonTerminating -> return baseValue
  T.TVar _ -> return baseValue
  T.TNum _ -> return baseValue
  T.TConstructor _ _ -> return baseValue
  T.TLam _ term -> recurseFun term
  T.THole -> return baseValue
  T.TLet letBindings mainTerm ->
    let (_, _, _, innerTerms) = unzip4 letBindings
    in do
      results <- mapM recurseFun (mainTerm:innerTerms)
      return $ combinator results
  T.TDummyBinds _ term -> recurseFun term
  T.TStackSpikes _ term -> recurseFun term
  T.THeapSpikes _ term -> recurseFun term
  T.TRedWeight _ red -> case red of
    T.RApp term _ -> recurseFun term
    T.RCase mainTerm caseStms ->
      let (_, _, innerTerms) = unzip3 caseStms
      in do
        results <- mapM recurseFun (mainTerm:innerTerms)
        return $ combinator results
    T.RPlusWeight term1 _ term2 -> do
      results <- mapM recurseFun [term1, term2]
      return $ combinator results
    T.RAddConst _ term -> recurseFun term
    T.RIsZero term -> recurseFun term
    T.RSeq term1 term2 -> do
      results <- mapM recurseFun [term1, term2]
      return $ combinator results


-- | same as applyOnSubterms, but for laws. Does not apply the recursive case
-- to the term that may be inside the VarSet of the TDummyBinds.
applyOnLawSubterms :: Law.Term
                      -> b
                      -> (Law.Term -> b)
                      -> ([b] -> b)
                      -> b
applyOnLawSubterms bigTerm baseValue recurseFun combinator = case bigTerm of
  Law.TValueMetaVar _        -> baseValue
  Law.TGeneralMetaVar _      -> baseValue
  Law.TMVTerms _             -> baseValue
  Law.TVar _                 -> baseValue
  Law.TAppCtx _ term         -> recurseFun term
  Law.TAppValCtx _ term      -> recurseFun term
  Law.TNonTerminating        -> baseValue
  Law.TNum _                 -> baseValue
  Law.TConstructor _         -> baseValue
  Law.TStackSpikes _ term    -> recurseFun term
  Law.THeapSpikes _ term     -> recurseFun term
  Law.TDummyBinds _ term     -> recurseFun term
  Law.TSubstitution term _ _ -> recurseFun term
  Law.TLam _ term            -> recurseFun term
  Law.TLet (Law.LBSBoth _metas moreConcreteBinds) term  ->
    combinator $ map recurseFun (term:innerTerms)
    where
      innerTerms = catMaybes $ map getInnerTerm moreConcreteBinds
      getInnerTerm (Law.LBConcrete _ _ _ term) = Just term
      getInnerTerm (Law.LBVectorized _ _ _ _) = Nothing
  Law.TRedWeight _ reduction -> case reduction of
    Law.RMetaVar _ term -> recurseFun term
    Law.RApp term _ -> recurseFun term
    Law.RPlusW term1 _ term2 -> combinator $ map recurseFun [term1, term2]
    Law.RCase term caseStms ->
      combinator $ map recurseFun (term:innerTerms)
      where
        innerTerms = catMaybes $ map getInnerTerm caseStms
        getInnerTerm (Law.CSAlts _) = Nothing
        getInnerTerm (Law.CSPatterns _ term) = Just term
        getInnerTerm (Law.CSConcrete _ term) = Just term
    Law.RAddConst _ term -> recurseFun term
    Law.RIsZero term -> recurseFun term
    Law.RSeq term1 term2 -> combinator $ map recurseFun [term1, term2]

-- | Like applyOnLawSubterms, but monadic
applyOnLawSubtermsM :: (Monad m) => Law.Term
                                    -> b
                                    -> (Law.Term -> m b)
                                    -> ([b] -> b)
                                    -> m b
applyOnLawSubtermsM bigTerm baseValue recurseFun combinator = case bigTerm of
  Law.TValueMetaVar _        -> return baseValue
  Law.TGeneralMetaVar _      -> return baseValue
  Law.TMVTerms _             -> return baseValue
  Law.TVar _                 -> return baseValue
  Law.TAppCtx _ term         -> recurseFun term
  Law.TAppValCtx _ term      -> recurseFun term
  Law.TNonTerminating        -> return baseValue
  Law.TNum _                 -> return baseValue
  Law.TConstructor _         -> return baseValue
  Law.TStackSpikes _ term    -> recurseFun term
  Law.THeapSpikes _ term     -> recurseFun term
  Law.TDummyBinds _ term     -> recurseFun term
  Law.TSubstitution term _ _ -> recurseFun term
  Law.TLam _ term            -> recurseFun term
  Law.TLet (Law.LBSBoth _metas moreConcreteBinds) term  -> do
    results <- mapM recurseFun (term:innerTerms)
    return $ combinator results
    where
      innerTerms = catMaybes $ map getInnerTerm moreConcreteBinds
      getInnerTerm (Law.LBConcrete _ _ _ term) = Just term
      getInnerTerm (Law.LBVectorized _ _ _ _) = Nothing
  Law.TRedWeight _ reduction -> case reduction of
    Law.RMetaVar _ term -> recurseFun term
    Law.RApp term _ -> recurseFun term
    Law.RPlusW term1 _ term2 -> do
      results <- mapM recurseFun [term1, term2]
      return $ combinator results
    Law.RCase term caseStms -> do
      results <- mapM recurseFun (term:innerTerms)
      return $ combinator results
      where
        innerTerms = catMaybes $ map getInnerTerm caseStms
        getInnerTerm (Law.CSAlts _) = Nothing
        getInnerTerm (Law.CSPatterns _ term) = Just term
        getInnerTerm (Law.CSConcrete _ term) = Just term
    Law.RAddConst _ term -> recurseFun term
    Law.RIsZero term -> recurseFun term
    Law.RSeq term1 term2 -> do
      results <- mapM recurseFun [term1, term2]
      return $ combinator results

-- | could not actually find any utility function for this, except in
-- Agda.Utils.List, which seems weird to import.
distinct :: (Eq a) => [a] -> Bool
distinct [] = True
distinct (x:xs) = (x `notElem` xs) && distinct xs

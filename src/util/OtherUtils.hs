{-# LANGUAGE FlexibleContexts #-}

module OtherUtils (applyOnSubTermsM, filterNoise) where

import Control.Monad.Except (MonadError, throwError)
import Data.List (zip4, unzip4)
import qualified Control.Monad.Logger as Log
import Data.List.Extra (replace)
import Data.Maybe (catMaybes)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law

-- | Given a monadic function on a term, applies it to all the subterms of a
-- term. Does not do anything with the variables, throws an error on terms
-- that do not contain subterms and reassembles the term after the monadic
-- computation has been applied to the subterm.
applyOnSubTermsM :: (Monad m, MonadFail m) =>
                    (T.Term -> m T.Term) -> T.Term -> m T.Term
applyOnSubTermsM f bigTerm = case bigTerm of
  T.TVar var -> fail "Contains no subterms"
  T.TNum integer -> fail "Contains no subterms"
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
  T.TRedWeight redWeight red1 -> do
    red2 <- case red1 of
              T.RApp term1 var -> do
                term2 <- f term1
                return $ T.RApp term2 var
              T.RPlusWeight subterm1 redWeight' subterm2 -> do
                subterm1' <- f subterm1
                subterm2' <- f subterm2
                return $ T.RPlusWeight subterm1' redWeight' subterm2'
    return $ T.TRedWeight redWeight red2

filterNoise :: String -> String
filterNoise = let removeChars = filter (\c -> c /='\"' && c /= '\n')
                  lessWhiteSpace = replace "  " " "
              in lessWhiteSpace . removeChars

-- | Given f1 and f2, it applies f1 to all subterms that are part of real
-- terms and f2 on all subterms that are part of . For terms that do not
-- contain subterms, it does nothing.
applyOnLawSubtermsM :: (Monad m) => Law.Term -> (Law.Term -> m ()) -> m ()
applyOnLawSubtermsM bigTerm f = case bigTerm of
  Law.TValueMetaVar _string -> undefined
  Law.TGeneralMetaVar _string -> undefined
  Law.TMVTerms _string -> undefined
  Law.TVar _string -> undefined
  Law.TAppCtx _string term -> undefined
  Law.TAppValCtx _string term -> undefined
  Law.TNonTerminating -> undefined
  Law.TNum _integer -> undefined
  Law.TConstructor _constructor -> undefined
  Law.TStackSpikes _intExpr term -> undefined
  Law.THeapSpikes _intExpr term -> undefined
  Law.TDummyBinds varSet term -> undefined
  Law.TSubstitution term _string1 _string2 -> undefined
  Law.TLam _string term -> undefined
  Law.TLet letBindings term -> undefined
  Law.TRedWeight intExpr reduction -> undefined

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

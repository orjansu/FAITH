{-# LANGUAGE FlexibleContexts #-}

module OtherUtils (applyOnSubTermsM, filterNoise) where

import Control.Monad.Except (MonadError, throwError)
import qualified MiniTypedAST as T
import Data.List (zip4, unzip4)
import qualified Control.Monad.Logger as Log
import Data.List.Extra (replace)

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

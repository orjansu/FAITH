{-# LANGUAGE FlexibleContexts #-}

module OtherUtils (assert, assertTerm) where

import Control.Monad.Except (MonadError, throwError)
import qualified MiniTypedAST as T
import ShowTypedTerm (showTypedTerm)

assert :: (MonadError String m) => Bool -> String -> m ()
assert True _ = return ()
assert False str = throwError $"Assertion failed: "++str

assertTerm :: (MonadError String m) => Bool -> String -> T.Term -> m ()
assertTerm True _ _ = return ()
assertTerm False str term = throwError $
  "Assertion "++str++" failed for term "++showTypedTerm term

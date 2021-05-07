{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module CheckMonad (CheckM
                  , runCheckM
                  , assert
                  , assertInternal
                  , assertTerm
                  , noSupport
                  , internalException
                  , throwCallstackError
                  ) where

import qualified Control.Monad.Logger as Log
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Text (pack, Text)
import qualified MiniTypedAST as T
import ShowTypedTerm (showTypedTerm)

newtype CheckM a = MkM {getM :: (ExceptT String
                                  (Log.WriterLoggingT Identity) a)}
  deriving (Functor, Applicative, Monad, Log.MonadLogger, MonadError String)

runCheckM :: CheckM a -> Either [String] a
runCheckM monadComputation =
  let r = runIdentity $
            Log.runWriterLoggingT $
                runExceptT $
                  getM $
                    monadComputation
  in case r of
    (Right a, logs) -> Right a
    (Left errorMsg, logs) -> Left $ (map toLine logs) ++ [errorMsg]

toLine :: Log.LogLine -> String
toLine (loc, logsource, loglevel, logstr) =
  show (loglevel, logstr)

assert :: (MonadError String m, Log.MonadLogger m, HasCallStack) =>
          Bool -> String -> m ()
assert True _ = return ()
assert False description = throwCallstackError $
  "assertion failed: "++description

assertTerm :: (MonadError String m, Log.MonadLogger m, HasCallStack) => Bool -> String -> T.Term -> m ()
assertTerm True _ _ = return ()
assertTerm False str term = throwCallstackError $
  "Assertion "++str++" failed for term "++showTypedTerm term

noSupport :: (MonadError String m, Log.MonadLogger m, HasCallStack)
             => String -> m a
noSupport spec = throwCallstackError $ spec ++ " not supported yet"

assertInternal :: (Log.MonadLogger m, MonadError String m, HasCallStack) =>
                  Bool -> String -> m ()
assertInternal True _ = return ()
assertInternal False description =
  internalException $ "Assertion failed: "++description

internalException :: (Log.MonadLogger m, MonadError String m, HasCallStack) =>
                     String -> m a
internalException description = do
  Log.logOtherCS callStack (Log.LevelOther (pack "Internal")) $ pack description
  throwCallstackError $ "Internal Error: "++description

throwCallstackError :: (Log.MonadLogger m, MonadError String m, HasCallStack) =>
  String -> m a
throwCallstackError descr =
  throwError $ "At "++ prettyCallStack callStack++"\n"++descr

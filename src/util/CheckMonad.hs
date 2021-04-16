{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module CheckMonad (CheckM
                  , runCheckM
                  , assert
                  , assertInternal
                  ) where

import qualified Control.Monad.Logger as Log
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Text (pack, Text)

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
  (show logstr)

assert :: (MonadError String m) => Bool -> String -> m ()
assert True _ = return ()
assert False description = throwError $ "assertion failed: "++description

assertInternal :: (Log.MonadLogger m, MonadError String m) =>
                  Bool -> String -> m ()
assertInternal True _ = return ()
assertInternal False description = do
  Log.logOtherN (Log.LevelOther (pack "InternalAssertion")) $ pack description
  throwError $ "Internal assertion failed: "++description

import System.Directory   (getHomeDirectory)
import System.Environment (getArgs)
import System.Exit        (die, exitFailure)
import System.FilePath    (dropExtension, replaceExtension, splitFileName)
import System.Process     (callProcess)
import System.IO (hPutStrLn, stderr, hGetLine, stdin, hGetContents, hPutStr,
                  stdout)

import ParSie                   (pProofScript, myLexer)
import PrintSie                 ( printTree )
import ErrM                     (Err)
import qualified AbsSie         as UT (ProofScript)
import qualified MiniTypedAST       as A (ProofScript)
import MiniTypeChecker              (typecheck)

-- | Main: read file passed by only command line argument and run compiler pipeline.
main :: IO ()
main = do
  input <- hGetContents stdin
  tree <- parse input
  putStrLn $ printTree tree
  return ()

-- | Parse file contents into AST.
parse :: String -> IO UT.ProofScript
parse s =
  case pProofScript (myLexer s) of
    Left err  -> do
      hPutStrLn stderr "ERROR"
      hPutStrLn stderr $ "Lexing error" ++ err
      exitFailure
    Right  tree -> return tree

-- | Type check and return a type-annotated program.
check :: UT.ProofScript -> IO A.ProofScript
check tree =
  case typecheck tree of
    Left err -> do
      hPutStrLn stderr "ERROR"
      hPutStrLn stderr $ "Type error " ++ err
      exitFailure
    Right tree' -> do
        hPutStrLn stderr "OK"
        return tree'

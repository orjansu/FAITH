import System.Directory   (getHomeDirectory)
import System.Environment (getArgs)
import System.Exit        (die, exitFailure)
import System.FilePath    (dropExtension, replaceExtension, splitFileName)
import System.Process     (callProcess)
import System.IO (hPutStrLn, stderr, hGetLine, stdin, hGetContents, hPutStr,
                  stdout, writeFile)
import Data.List (intersperse, concat)

import ParSie                   (pProofScript, myLexer)
import PrintSie                 ( printTree )
import ErrM                     (Err)
import qualified AbsSie         as UT (ProofScript)
import qualified MiniTypedAST       as T (ProofScript)
import MiniTypeChecker              (typecheck)
import ProofChecker                 (checkDetailedProof)

-- | Main: read file passed by only command line argument and run compiler pipeline.
main :: IO ()
main = do
  input <- hGetContents stdin
  tree <- parse input
  tTree <- runTypecheck tree
  runCheckDetailedProof tTree
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
runTypecheck :: UT.ProofScript -> IO T.ProofScript
runTypecheck tree =
  case typecheck tree of
    Left err -> do
      hPutStrLn stderr "ERROR"
      hPutStrLn stderr $ "Type error " ++ err
      exitFailure
    Right tree' -> do
        hPutStrLn stderr "No type errors"
        return tree'

runCheckDetailedProof :: T.ProofScript -> IO ()
runCheckDetailedProof tTree =
  case checkDetailedProof tTree of
    Nothing -> hPutStrLn stderr "Proof is correct"
    Just errorMsgs -> do
      let relevantMsgs = take 11 errorMsgs
      hPutStrLn stderr "Error when checking proof. Last 10 logs and error:"
      mapM (hPutStrLn stderr) relevantMsgs
      let fullLog = concat $ intersperse "\n " errorMsgs
      let logFile = "gen/proofLog.txt"
      writeFile logFile fullLog
      hPutStrLn stderr $ "Full logs can be found in "++logFile

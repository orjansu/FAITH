import System.Directory   (getHomeDirectory)
import System.Environment (getArgs)
import System.Exit        (die, exitFailure)
import System.FilePath    (dropExtension, replaceExtension, splitFileName)
import System.Process     (callProcess)
import System.IO (hPutStrLn, stderr, hGetLine, stdin, hGetContents, hPutStr,
                  stdout, writeFile)
import Data.List (intersperse, concat)

import qualified ParSie (pProofScript, myLexer)
import qualified ParSieLaws (pLawList, myLexer)
import ErrM                     (Err)
import qualified AbsSie         as UT (ProofScript)
import qualified MiniTypedAST       as T (ProofScript)
import qualified AbsSieLaws as UTLaw (LawList)
import qualified TypedLawAST as TLaw (LawMap)
import LawTypeChecker (typecheckLaws)
import MiniTypeChecker (typecheckProof)
import ProofChecker                 (checkDetailedProof)

-- | Main: read file passed by only command line argument and run compiler pipeline.
main :: IO ()
main = do
  (lawInput, proofInput) <- getInputs
  putStrLn "Parsing law file"
  lawTree <- parse lawInput (ParSieLaws.pLawList . ParSieLaws.myLexer)
  tLaws <- runTypecheckLaws lawTree
  putStrLn "Parsing proof file"
  proofTree <- parse proofInput (ParSie.pProofScript . ParSie.myLexer)
  tProofScript <- runTypecheckProof proofTree tLaws
  runCheckDetailedProof tProofScript

getInputs :: IO (String, String)
getInputs = do
  args <- getArgs
  case args of
    (lawFile:proofFile:[]) -> do
      putStrLn $ "Using the laws in "++lawFile
                ++" to check the proofs in "++proofFile
      lawInput <- readFile lawFile
      proofInput <- readFile proofFile
      return (lawInput, proofInput)
    _ -> do
      putStrLn $ "usage: ./sie <law-file> <proof-file>"
      exitFailure

-- | Parse file contents into AST.
parse :: String -> (String -> Either String a) -> IO a
parse s parseFun =
  case parseFun s of
    Left err  -> do
      hPutStrLn stderr "ERROR"
      hPutStrLn stderr $ "Lexing error: " ++ err
      exitFailure
    Right  tree -> return tree

runTypecheckLaws :: UTLaw.LawList -> IO TLaw.LawMap
runTypecheckLaws utLawList =
  case typecheckLaws utLawList of
    Left errors -> do
      hPutStrLn stderr "Type error in law file:"
      mapM (hPutStrLn stderr) errors
      exitFailure
    Right lawMap -> return lawMap

runTypecheckProof :: UT.ProofScript -> TLaw.LawMap -> IO T.ProofScript
runTypecheckProof proofScript lawMap =
  case typecheckProof proofScript lawMap of
    Left err -> do
      hPutStrLn stderr "ERROR"
      hPutStrLn stderr $ "Type error: " ++ err
      exitFailure
    Right tree' -> return tree'

runCheckDetailedProof :: T.ProofScript -> IO ()
runCheckDetailedProof tTree =
  case checkDetailedProof tTree of
    Nothing -> hPutStrLn stderr "Proof is correct"
    Just errorMsgs -> do
      let relevantMsgs = take 11 errorMsgs
      hPutStrLn stderr "Error when checking proof. Last 10 logs and error:"
      mapM (hPutStrLn stderr) relevantMsgs
      let fullLog = concat $ intersperse "\n " errorMsgs
      let logFile = "proofLog.txt"
      writeFile logFile fullLog
      hPutStrLn stderr $ "Full logs can be found in "++logFile

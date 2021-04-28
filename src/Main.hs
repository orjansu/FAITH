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
import Matcher (addProofDetails)

-- | Main: read file passed by only command line argument and run compiler pipeline.
main :: IO ()
main = do
  (lawInput, proofInput) <- getInputs
  putStr "Parsing law file..."
  lawTree <- parse lawInput (ParSieLaws.pLawList . ParSieLaws.myLexer)
  tLaws <- runTypecheckLaws lawTree
  parseAndCheckDetailedProof tLaws proofInput
  --proofTree <- parse proofInput (ParSie.pProofScript . ParSie.myLexer)
  --tAbstractProofScript <- runTypecheckProof proofTree tLaws
  --tDetailedProofScripts <- undefined
  --undefined


-- | checking of a detailed proof where no matching or other guessing is
-- involved. Inputs: the parsed laws and the unparsed proof script
parseAndCheckDetailedProof :: TLaw.LawMap -> String -> IO ()
parseAndCheckDetailedProof tLaws proofInput = do
  putStr "Parsing detailed proof file..."
  proofTree <- parse proofInput (ParSie.pProofScript . ParSie.myLexer)
  tProofScript <- runTypecheckProof proofTree tLaws
  runCheckDetailedProof tProofScript
  putStrLn "Proof is correct"


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
      putStrLn "ERROR"
      putStrLn $ "Lexing error: " ++ err
      exitFailure
    Right  tree -> do
      putStrLn "Successful"
      return tree

runTypecheckLaws :: UTLaw.LawList -> IO TLaw.LawMap
runTypecheckLaws utLawList = do
  putStr "Typechecking law file..."
  handleResult (typecheckLaws utLawList) "proofLog.txt"

runTypecheckProof :: UT.ProofScript -> TLaw.LawMap -> IO T.ProofScript
runTypecheckProof proofScript lawMap = do
  putStr "Type-checking detailed proofFile..."
  case typecheckProof proofScript lawMap of
    Left err -> do
      putStrLn "ERROR"
      putStrLn $ "Type error: " ++ err
      exitFailure
    Right tree' -> do
      putStrLn "Successful"
      return tree'

runCheckDetailedProof :: T.ProofScript -> IO ()
runCheckDetailedProof tTree = do
  putStr "Checking detailed proof..."
  handleResult (checkDetailedProof tTree) "proofLog.txt"

printErrorMsgsAndExit :: [String] -> String -> IO a
printErrorMsgsAndExit errorMsgs logFileName = do
  let relevantMsgs = drop (length errorMsgs - 11) errorMsgs
  putStrLn "Last 10 logs and error:"
  mapM (putStrLn) relevantMsgs
  let fullLog = concat $ intersperse "\n " errorMsgs
  writeFile logFileName fullLog
  putStrLn $ "Full logs can be found in "++logFileName
  exitFailure

handleResult :: Either [String] a -> String -> IO a
handleResult result logFileName = case result of
  Left errorMsgs -> do
    putStrLn "ERROR"
    printErrorMsgsAndExit errorMsgs logFileName
  Right result -> do
    putStrLn "Successful"
    return result

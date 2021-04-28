import System.Directory   (getHomeDirectory)
import System.Environment (getArgs)
import System.Exit        (die, exitFailure)
import System.FilePath    (dropExtension, replaceExtension, splitFileName)
import System.Process     (callProcess)
import System.IO (hPutStrLn, stderr, hGetLine, stdin, hGetContents, hPutStr,
                  stdout, writeFile)
import Data.List (intersperse, concat)
import Data.Either (rights, isRight)
import Util (filterByList)

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
  (lawInput, proofInput, proofFile) <- getInputs
  putStr "Parsing law file..."
  lawTree <- parse lawInput (ParSieLaws.pLawList . ParSieLaws.myLexer)
  tLaws <- runTypecheckLaws lawTree
  parseAndCheckDetailedProof tLaws proofInput
  proofTree <- parse proofInput (ParSie.pProofScript . ParSie.myLexer)
  tAbstractProofScript <- runTypecheckProof proofTree tLaws
  putStr "Adding details via matching..."
  detailedUnchecked <- handleResult (addProofDetails tAbstractProofScript)
                                    "proofLog.txt"
  corrDetailedProofs <- getCorrectProofs detailedUnchecked
  saveProofs corrDetailedProofs proofFile
  putStrLn "There is a correct detailed version of your proof, but since I haven't implemented pretty-printing yet, I can't print the detailed proof yet."

getCorrectProofs :: [T.ProofScript] -> IO [T.ProofScript]
getCorrectProofs detailedUnchecked = do
  let results = map checkDetailedProof detailedUnchecked
  let correctResults = rights results
  if correctResults == []
    then do
      let outFile = "proofLog.txt"
      putStrLn $ "No correct proofs found. "
        ++"Writing attempts and errors in "++outFile
      let errorReport = concat
                        . intersperse separator
                        . map logProofErrors
                        $ zip results detailedUnchecked
      writeFile outFile errorReport
      exitFailure
    else return $ filterByList (map isRight results) detailedUnchecked
  where
    separator = "==================================================\n"
    logProofErrors :: (Either [String] (), T.ProofScript) -> String
    logProofErrors (Left errorMsgs, proof) =
      "-----------POSSIBLE PROOF------------\n"
      ++showProof proof++"\n"
      ++"-------------ERRORS----------------\n"
      ++"Final error: "++last errorMsgs++"\n"
      ++"complete log: \n"
      ++(concat . intersperse "\n" $ errorMsgs)

showProof :: T.ProofScript -> String
showProof proofScript = "for now: "++show proofScript

saveProofs :: [T.ProofScript] -> String -> IO ()
saveProofs (proofScript:[]) origFileName = do
  let filename = origFileName ++"_detailed"
  writeFile (showProof proofScript) filename
  putStrLn $ "Detailed proof can be found in "++filename
saveProofs proofScripts origFileName = do
  let fileNames = map (\n -> origFileName++"_detailed"++show n)
                      [1..length proofScripts]
  mapM (\(p, fn) -> writeFile (showProof p) fn) $ zip proofScripts fileNames
  putStrLn $ "Detailed proofs written to "++show fileNames

-- | checking of a detailed proof where no matching or other guessing is
-- involved. Inputs: the parsed laws and the unparsed proof script
parseAndCheckDetailedProof :: TLaw.LawMap -> String -> IO ()
parseAndCheckDetailedProof tLaws proofInput = do
  putStr "Parsing detailed proof file..."
  proofTree <- parse proofInput (ParSie.pProofScript . ParSie.myLexer)
  tProofScript <- runTypecheckProof proofTree tLaws
  runCheckDetailedProof tProofScript
  putStrLn "Proof is correct"


getInputs :: IO (String, String, String)
getInputs = do
  args <- getArgs
  case args of
    (lawFile:proofFile:[]) -> do
      putStrLn $ "Using the laws in "++lawFile
                ++" to check the proofs in "++proofFile
      lawInput <- readFile lawFile
      proofInput <- readFile proofFile
      return (lawInput, proofInput, proofFile)
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

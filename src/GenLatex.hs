import System.Directory   (getHomeDirectory)
import System.Environment (getArgs)
import System.Exit        (die, exitFailure)
import System.FilePath    (dropExtension, replaceExtension, splitFileName)
import System.Process     (callProcess)
import System.IO (hPutStrLn, stderr, hGetLine, stdin, hGetContents, hPutStr,
                  stdout)

import ParSieLaws                   (pSieLaws, myLexer)
import PrintGenLatexLaws                 ( printTree )
import ErrM                     (Err)
import qualified AbsSieLaws         as UT (ProofScript)
import MiniTypeChecker              (typecheck)

-- | Main: read file passed by only command line argument and run compiler pipeline.
main :: IO ()
main = do
  input <- hGetContents stdin
  tree <- parse input
  latex <- toLatex tree
  printTree latex
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

toLatex = undefined

module LawTypeChecker (typecheckLaws) where

import qualified AbsSieLaws as UTLaw
import qualified TypedLawAST as TLaw

typecheckLaws :: UTLaw.LawList -> Either [String] TLaw.LawMap
typecheckLaws lawList = undefined

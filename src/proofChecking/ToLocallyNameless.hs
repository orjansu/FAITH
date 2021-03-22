{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module ToLocallyNameless
    (
    toLocallyNameless
    ) where

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.State (StateT, MonadState, runStateT, gets, modify)
import Data.Functor.Identity (Identity, runIdentity)
import Data.List (zip, unzip4)

import qualified MiniTypedAST as T
import qualified LocallyNameless as LNL


type VarName = String
type Distance = Integer
type VarIndex = Integer
data LNLSt = MkLNLSt { lambdaVars :: Map.Map VarName Distance
                     , letVars :: Map.Map VarName (Distance, VarIndex)
                     , caseVars :: Map.Map VarName (Distance, VarIndex)
                     , freeVars :: Set.Set VarName
                     }

initLNLSt :: LNLSt
initLNLSt = MkLNLSt { lambdaVars = Map.empty
                    , letVars = Map.empty
                    , caseVars = Map.empty
                    , freeVars = Set.empty
                    }

newtype LNLMonad a = Mk {getM :: (ExceptT String (StateT LNLSt Identity) a)}
  deriving (Functor, Applicative, Monad, MonadState LNLSt, MonadError String)

instance MonadFail LNLMonad where
  fail str = throwError str

-- | Converts the term to a locally nameless representation, as specified
-- by the data structure in LocallyNameless.hs . Assumes that all named
-- variables in the input term are distinct. Throws errors if there is an
-- internal error in its implementation or the input data. Also returns the
-- set of free variables found in the expression.
toLocallyNameless :: T.Term -> Either String (LNL.Term, Set.Set VarName)
toLocallyNameless term =
  let (res, state) = runIdentity (
                       runStateT (
                         runExceptT(
                          getM (
                            computeLNLTerm term
                          )
                         )
                       ) initLNLSt
                     )
  in case res of
    Left errorMsg -> Left errorMsg
    Right lnlTerm -> Right (lnlTerm, freeVars state)

computeLNLTerm :: T.Term -> LNLMonad LNL.Term
computeLNLTerm (T.TVar varName) = do
  lnlVar <- computeLNLVar varName
  return $ LNL.TVar lnlVar
computeLNLTerm (T.TNum n) = return $ LNL.TNum n
computeLNLTerm (T.THole) = return $ LNL.THole
computeLNLTerm (T.TLam varName term) = do
  -- 1. Increase the distance on all current lambdas
  lambdaVars0 <- gets lambdaVars
  let increaseDistance = (\distance -> distance +1)
  let lambdaVars1 = Map.map increaseDistance lambdaVars0
  -- 2. Bind the current variable to distance 0
  let lambdaVars2 = Map.insert varName 0 lambdaVars1
  modify (\st -> st{lambdaVars = lambdaVars2})
  -- 3. Compute the new lnl Term
  lnlTerm <- computeLNLTerm term
  -- 4. Decrease the distance on all current lambdas
  lambdaVars3 <- gets lambdaVars
  let decreaseDistance = (\distance -> distance -1)
  let lambdaVars4 = Map.map decreaseDistance lambdaVars3
  -- 5. Remove all lambdas with distance =< 0.
  --    you should now arrive at the previous lambda bindings.
  --    This check increases the memory complexity, so I might remove it later.
  let lambdaVars5 = Map.filter (>= 0) lambdaVars4
  modify (\st -> st{lambdaVars = lambdaVars5})
  if lambdaVars0 == lambdaVars5
    then return ()
    else fail "Internal error: assertion on lambda bindings failed."
  --6. Return a lnl lambda with the new lnl term
  return $ LNL.TLam lnlTerm
computeLNLTerm (T.TLet letBinds mainTerm) = do
  -- 1. Increase the distance on all current let variables
  letVars0 <- gets letVars
  let increaseDistance = (\(distance, varIndex) -> (distance+1, varIndex))
  let letVars1 = Map.map increaseDistance letVars0
  modify (\st -> st{letVars = letVars1})
  -- 2. Bind each variable name x0...xi...xn to (0, i) in the let-map
  let (varNames, stackweights, heapweights, terms) = unzip4 letBinds
  let distance_index          = zip (repeat 0) [0..]
  let varName__distance_index = zip varNames distance_index
  let newVar_set              = Map.fromList varName__distance_index
  letVars2 <- gets letVars
  if newVar_set `Map.disjoint` letVars2
    then return ()
    else fail "Internal error: let binding names are not unique"
  let letVars3 = letVars2 `Map.union` newVar_set
  modify (\st -> st{letVars = letVars3})
  -- 3. Convert the inner terms to lnl
  -- 3.1 Convert each term bound in the let-bindings to a Locally Nameless
  -- representation
  lnlTerms <- mapM computeLNLTerm terms
  -- 3.2 Convert the main term to Locally Nameless representation
  lnlMainTerm <- computeLNLTerm mainTerm
  -- 4. Decrease distance on all current let-variables
  letVars4 <- gets letVars
  let decreaseDistance = (\(distance, varIndex) -> (distance-1, varIndex))
  let letVars5 = Map.map increaseDistance letVars4
  modify (\st -> st{letVars = letVars5})
  -- 5. Remove all variables with negative distance. We should now arrive at the
  -- same bindings as before the let-term
  letVars6 <- gets letVars
  let letVars7 = Map.filter (\(distance, _index) -> distance >= 0) letVars6
  modify (\st -> st{letVars = letVars7})
  if letVars0 == letVars7
    then return ()
    else fail "Internal error: let-binding has faulty implementation"
  -- 6. Create the new complete lnl term
  -- 6.1 Convert the weights. These should be equal in both representations.
  -- TODO convert the weight expressions when these are added to the language
  let lnlStackWeights = stackweights
  let lnlHeapWeights = heapweights
  -- 6.2 Return a new let, with all the lnl terms
  let lnlLetBindings = zip3 lnlStackWeights lnlHeapWeights lnlTerms
  return $ LNL.TLet lnlLetBindings lnlMainTerm
computeLNLTerm (T.TDummyBinds varSet term) = do
  lnlTerm <- computeLNLTerm term
  let varList = Set.toList varSet
  lnlVarList <- mapM computeLNLVar varList
  let lnlVarSet = Set.fromList lnlVarList
  return $ LNL.TDummyBinds lnlVarSet lnlTerm
computeLNLTerm (T.TRedWeight redWeight reduction) = do
  lnlReduction <- computeLNLReduction reduction
  let lnlRedWeight = redWeight
  return $ LNL.TRedWeight lnlRedWeight lnlReduction

computeLNLVar :: VarName -> LNLMonad LNL.Var
computeLNLVar varName = do
  lamRepr <- fmap (Map.lookup varName) (gets lambdaVars)
  letRepr <- fmap (Map.lookup varName) (gets letVars)
  caseRepr <- fmap (Map.lookup varName) (gets caseVars)
  case (lamRepr, letRepr, caseRepr) of
    (Just distance, Nothing, Nothing) ->
      return $ LNL.LambdaVar distance
    (Nothing, Just (distance, varIndex), Nothing) ->
      return $ LNL.LetVar distance varIndex
    (Nothing, Nothing, Just (distance, varIndex)) ->
      return $ LNL.CaseConstructorVar distance varIndex
    (Nothing, Nothing, Nothing) -> do
      -- Add the free variable to the set of free variables
      modify (\st -> st{freeVars = Set.insert varName (freeVars st)})
      return $ LNL.FreeVar varName
    (_, _, _) -> fail $ "Internal error: "++varName++" is bound to several "
      ++"kinds of binding sites"

computeLNLReduction :: T.Red -> LNLMonad LNL.Red
computeLNLReduction (T.RApp term var) = do
  lnlTerm <- computeLNLTerm term
  lnlVar <- computeLNLVar var
  return $ LNL.RApp lnlTerm lnlVar
computeLNLReduction (T.RPlusWeight term1 redWeight term2) = do
  lnlTerm1 <- computeLNLTerm term1
  let lnlRedWeight = redWeight
  lnlTerm2 <- computeLNLTerm term2
  return $ LNL.RPlusWeight lnlTerm1 lnlRedWeight lnlTerm2

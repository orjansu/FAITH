{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

module ProofChecker where

import qualified Control.Monad.Logger as Log
import Data.Text (pack)

import qualified MiniTypedAST as T
import qualified TypedLawAST as Law


--checkSubstitution :: Law.Term -> Law.Substitutions ->

applySubstitution :: (MonadFail m) => Law.Term -> Law.Substitutions -> m T.Term
applySubstitution = undefined


class AlphaEquivalentCheckable a where
  type ContextInfo a
  checkAlphaEq :: (MonadFail m, Log.MonadLogger m)
                            => ContextInfo a -> a -> a -> m ()
  -- A () means that they are alpha equivalent. Otherwise an error
  -- should be thrown.
{-
instance AlphaEquivalentCheckable T.Term where
  type ContextInfo T.Term = () -- Ett record med nivå på Lambda, Let, och CaseConstructor.
  -- | Assumes that all relevant De Bruijn indexes are calculated and correct,
  -- and that all variables refers to unique bind sites - i.e. new names must
  -- be unique with respect to the whole term.
  checkAlphaEq fv (T.TVar var1) (T.TVar var2) = undefined
  checkAlphaEq fv (T.TNum i1) (T.TNum i2) = undefined
  checkAlphaEq fv (T.THole) (T.THole) = undefined
  checkAlphaEq fv (T.TLet letBindings1 t1) (T.TLet letBindings2 t2) = undefined
  checkAlphaEq fv (T.TDummyBinds varset1 t1)
                  (T.TDummyBinds varset2 t2) = undefined
  checkAlphaEq fv (T.TRedWeight weight1 reduction1)
                  (T.TRedWeight weight2 reduction2) = undefined

type AreFree = Bool
instance AlphaEquivalentCheckable T.Var where
  type ContextInfo T.Var = AreFree
  -- | Checks if two variables are alpha equivalent. It does this by checking
  -- if the names are equivalent if the variables are free, and if they are
  -- bound, it checks if the de Bruijn representation is the same. The function
  -- therefore assumes that every variable name refers to a unique bind site
  -- and that the variables are either both subterms of the same term or that
  -- equivalence is checked between the start and goal. This function does not
  -- behave correctly for checking alpha equivalence between subterms of
  -- different terms, since two separate terms may have the same name for
  -- different bind sites.
  --
  -- The reason that the return type is () rather than a proof is that a proof
  -- type would require type-level Strings (and Integers), which is too much
  -- for the current scope of the project.
  checkAlphaEq :: (MonadFail m, Log.MonadLogger m)
                            => AreFree -> T.Var -> T.Var -> m ()
  checkAlphaEq True (T.DVar name1 _) (T.DVar name2 _)
    | name1 == name2 = return ()
    | name1 /= name2 = fail $ "variables "++name1++" and "++name2++" "
        ++"are both free and not equivalent because they have different names."
  checkAlphaEq False (T.DVar name1 deBruijn1)
                             (T.DVar name2 deBruijn2) = do
    Log.logInfoN . pack $ "variables "++name1++" and "++name2++" are bound. "
      ++ "Checking alpha equivalence."
    case (deBruijn1, deBruijn2) of
      (T.Lambda i1, T.Lambda i2)
        | i1 == i2 -> return ()
        | i1 /= i2 -> fail "bound to lambdas at different levels."
      (T.Let dist1 index1, T.Let dist2 index2)
        | dist1 == dist2 && index1 == index2 -> return ()
        | dist1 /= dist2 -> fail "bound to let:s at different levels."
        | index1 /= index2 -> fail $ "bound to different expressions within "
          ++"same order let:s. Might help to reorder the expressions in the " ++"let."
      (T.CaseConstructor dist1 index1, T.CaseConstructor dist2 index2)
        | dist1 == dist2 && index1 == index2 -> return ()
        | dist1 /= dist2 -> fail $ "bound to case-constructors at different "
          ++ "levels"
        | index1 /= index2 -> fail $ "bound to different variables in similar "
          ++ "case-constructor."
      (T.NoDeBruijn, T.NoDeBruijn) -> fail $ "internal error. Variables are "
        ++"bound but do not contain De Bruijn indexing."
      _ -> fail "bound to different kinds of constructs."
-}

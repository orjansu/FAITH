{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Common where
-- | Includes the language constructs that are the same between the language for
-- different representations of the Typed (supported) language. For example,
-- the representation of improvement relations is the same for the law language
-- and the normal proof language.
--
-- The file will only include constructs that are supported, and will thus not
-- initially support all types contained in the Abs[...].hs files.


import qualified Prelude as C (Eq, Ord, Show, Read, show)

-- Just deals with this one right now.
-- TODO as this is expanded, add clauses to LanguageLogic.hs
data ImpRel
  = DefinedEqual
  | StrongImprovementLR
  | WeakImprovementLR
  | StrongCostEquiv
  | WeakCostEquiv
  deriving (C.Eq, C.Ord, C.Read)

instance C.Show ImpRel where
  show DefinedEqual = "=def="
  show StrongImprovementLR = "|~>"
  show WeakImprovementLR = "|~~>"
  show StrongCostEquiv = "<~>"
  show WeakCostEquiv = "<~~>"

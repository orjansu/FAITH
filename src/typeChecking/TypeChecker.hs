module TypeChecker where
import qualified AbsSie as UT

typecheck = undefined;


-- | Matches the first term on the second term. If the terms do not match, it
-- returns the (Term, Term) pair that does not match, and if they do match, it
-- returns a list of the terms matching the ? signs. Uses equality of variable
-- representations as defined by their equality operation (==).
-- Improvements:
--  - ? on letbinds, integerExpressions -> better return type (SOP)
--  - general way of writing?
--  - SOP for errors (for idents etc)

matchTerm :: UT.Term -> UT.Term -> Either (UT.Term, UT.Term) [UT.Term]
matchTerm term UT.TAny = return [term]
matchTerm (UT.TLam x1 e1) (UT.TLam x2 e2) =
  if x1 == x2
    then matchTerm e1 e2
    else Left (UT.TLam x1 e1, UT.TLam x2 e2)
matchTerm (UT.TLet lbs1 e1) (UT.TLet lbs2 e2) =
  if lbs1 == lbs2
    then matchTerm e1 e2
    else Left (UT.TLet lbs1 e1, UT.TLet lbs2 e2)
matchTerm (UT.TStackSpike e1) (UT.TStackSpike e2) = matchTerm e1 e2
matchTerm (UT.TStackSpikes sw1 e1) (UT.TStackSpikes sw2 e2) =
  if sw1 == sw2
    then matchTerm e1 e2
    else Left (UT.TStackSpikes sw1 e1, UT.TStackSpikes sw2 e2)
matchTerm (UT.THeapSpike e1) (UT.THeapSpike e2) = matchTerm e1 e2
matchTerm (UT.THeapSpikes hw1 e1) (UT.THeapSpikes hw2 e2) =
  if hw1 == hw2
    then matchTerm e1 e2
    else Left (UT.THeapSpikes hw1 e1, UT.THeapSpikes hw2 e2)
matchTerm (UT.TDummyBinds vs1 e1) (UT.TDummyBinds vs2 e2) =
  if vs1 == vs2
    then matchTerm e1 e2
    else Left (UT.TDummyBinds vs1 e1, UT.TDummyBinds vs2 e2)
matchTerm (UT.TRedWeight rw r) _ = undefined
matchTerm (UT.TRed r) _ = undefined
matchTerm nonrecursive1 nonrecursive2 = if nonrecursive1 == nonrecursive2
                                        then return []
                                        else Left (nonrecursive1, nonrecursive2)

matchReduction :: UT.Red -> UT.Red -> Either (UT.Red, UT.Red) [UT.Red]
matchReduction (UT.RCase t1 stms1) (UT.RCase t2 stms2) = undefined
--matchReduction (RApp t1 var1) (RApp t1 var2) = undefined
--matchReduction (RAppInd var1 ie1 var1) (RAppInd var1 ie1 var1) = undefined
--matchReduction (RAddConst n t) (RAddConst n t) = undefined
--matchReduction (RIsZero t) (RIsZero t) = undefined
--matchReduction (RSeq t t) (RSeq t t) = undefined
--matchReduction (RPlusWeight t rw t) (RPlusWeight t rw t) = undefined
--matchReduction (RPlus t t) (RPlus t t) = undefined

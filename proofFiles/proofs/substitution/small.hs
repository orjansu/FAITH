-- single line comments
{- Multiple line
   Comments
-}
bindings{
-- Let-bindings for derivations in context
A = { false = False
    , head = \xs . case xs of {y : ys -> y}};
-- Constructor declaration
Pair (2);
Tripple (3);
Nothing (0);
}

proposition: A free(a b) |- s^(\c. a + b + c) |~> (\c. a + b + c);
proof: -simple -single{
  -spike-algebra-13
    ctx = (let A in [.])
    M=(\c. a + b + c)
    w=1;
  |~>
  -- note that we have to supply the |~>, but not the first and
  -- last term if we don't want to.
}qed;

-- There may be multiple proofs in a single file
proposition: A free(x) |- [1]h^[2]h^x <~> [2]h^[1]h^x;
proof: -simple -single{
  -spike-algebra-12-lr
    ctx =(let A in [.]) w=1 v=2 M=x;
  <~>
}qed;

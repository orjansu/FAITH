bindings {
G = {repeat =[0,0]= \x1. let {zs = repeat x1} in x1:zs};
}

-- base case
proposition: G free(x f) |- let {xs = {repeat}d^@ x} in f <> x <> xs
                        |~> let {xs = x : xs} in f <> x <> xs;
proof: -simple -single{
  -dummy-ref-algebra-8
    ctx=(let G in let {xs = [.] x} in f <> x <> xs)
    X={repeat}
    M=@;
  |~> let {xs = @ x} in f <> x <> xs;
  -@-rules-3-lr
    ctx = (let G in let {xs = [.]} in f <> x <> xs)
    R=([.] x);
  <~> let {xs = {x}d^@} in f <> x <> xs;
  -@-rules-2
    ctx=(let G in [.])
    G=let {}
    x=xs
    X={x}
    N=(f <> x <> xs)
    M=(x:xs);
  |~> let {xs = x : xs} in f <> x <> xs;
} qed;

--inductive case (before induction)
proposition: G free(x f) |- let {xs = [0]s^(\x2. let {ys = repeat x2}
                                                in x : ys) x} in f <> x <> xs
                        |~> let { xs = let {g =[0,0]= (\a . \ as . a : as)}
                                       in let {ys = repeat x} in g <> x <> ys}
                            in f <> x <> xs;
proof: -simple -single{
  -spike-algebra-zero-stack-spike-lr
    ctx=(let G in let {xs= [.] x} in f <> x <> xs)
    M=(\x2. let {ys = repeat x2} in x : ys);
  <~> let {xs = (\x2. let {ys = repeat x2} in x : ys) x} in f <> x <> xs;
  -reduction-lr
    ctx=(let G in let {xs = [.]} in f <> x <> xs)
    w=1
    R=([.] x)
    V=(\x2. let {ys = repeat x2} in x : ys)
    X={}
    N=(let {ys' = repeat x} in x : ys');
  <~> let {xs = s^{}d^(let {ys = repeat x} in x : ys)} in f <> x <> xs;
  -dummy-ref-algebra-5-lr
    ctx=(let G in let {xs = s^[.]} in f <> x <> xs)
    M=(let {ys = repeat x} in x : ys);
  <~> let {xs = s^(let {ys = repeat x} in x : ys)} in f <> x <> xs;
  -spike-algebra-13
    ctx=(let G in let {xs = [.]} in f <> x <> xs)
    w=1
    M=(let {ys = repeat x} in x : ys);
  |~> let {xs = let {ys = repeat x} in x : ys} in f <> x <> xs;
  -- Start of extra work needed because meta-variable M is not implemented.
  -dummy-ref-algebra-5-rl
    ctx=(let G in let {xs = let {ys = repeat x} in [.]} in f <> x <> xs)
    M=(x : ys);
  <~> let {xs = let {ys = repeat x} in {}d^(x : ys)} in f <> x <> xs;
  -spike-algebra-zero-stack-spike-rl
    ctx=(let G in let {xs = let {ys = repeat x} in [.]} in f <> x <> xs)
    M=({}d^(x : ys));
  <~> let {xs = let {ys = repeat x} in [0]s^{}d^(x : ys)} in f <> x <> xs;
  -reduction-rl
    ctx=(let G in let {xs = let {ys = repeat x} in [.]} in f <> x <> xs)
    N=(x : ys)
    w=0
    X={}
    R=([.] ys)
    V=(\as . x : as);
  <~> let {xs = let {ys = repeat x} in (\as . x : as) <> ys} in f <> x <> xs;
  -dummy-ref-algebra-5-rl
    ctx = (let G in let {xs = let {ys = repeat x}
                              in [.] <> ys} in f <> x <> xs)
    M=(\as . x : as);
  <~> let {xs = let {ys = repeat x}
                in {}d^(\as . x : as) <> ys}
      in f <> x <> xs;
  -spike-algebra-zero-stack-spike-rl
    ctx= (let G in let {xs = let {ys = repeat x}
                             in [.] <> ys} in f <> x <> xs)
    M=({}d^(\as . x : as));
  <~> let {xs = let {ys = repeat x} in [0]s^{}d^(\as . x : as) <> ys}
      in f <> x <> xs;
  -reduction-rl
    ctx= (let G in let {xs = let {ys = repeat x}
                             in [.] <> ys} in f <> x <> xs)
    w=0
    X={}
    N=(\as' . x : as')
    R=([.] x)
    V=(\a. \as . a : as);
  <~> let {xs = let {ys = repeat x} in (\a. \as . a : as) <> x <> ys}
                                    in f <> x <> xs;
  -spike-algebra-zero-heap-spike-rl
    ctx=(let G in let {xs = let {ys = repeat x}
                            in [.] <> x <> ys}
                  in f <> x <> xs)
    M=(\a. \as . a : as);
  <~> let {xs = let {ys = repeat x}
                in [0]h^(\a. \as . a : as) <> x <> ys}
      in f <> x <> xs;
  -let-elim-rl
    ctx=(let G in let {xs = let {ys = repeat x}
                            in [.] <> x <> ys}
                  in f <> x <> xs)
    M=(\a. \as . a : as)
    x=g
    v=0
    w=0;
  <~> let {xs = let {ys = repeat x}
                in (let {g =[0,0]= (\a. \as . a : as)} in g) <> x <> ys}
      in f <> x <> xs;
  -let-R-rl
    ctx=(let G in let {xs = let {ys = repeat x}
                         in [.] <> ys}
               in f <> x <> xs)
    G=let {g =[0,0]= (\a. \as . a : as)}
    M=g
    R=([.] x)
    w=0;
  <~> let {xs = let {ys = repeat x}
                in (let {g =[0,0]= (\a. \as . a : as)} in g <> x) <> ys}
      in f <> x <> xs;
  -let-R-rl
    ctx = (let G in let {xs = let {ys = repeat x}
                              in [.]}
                    in f <> x <> xs)
    G=let {g =[0,0]= (\a. \as . a : as)}
    M=(g <> x)
    R=([.] ys)
    w=0;
  <~> let {xs = let {ys = repeat x}
                in let {g =[0,0]= (\a. \as . a : as)} in g <> x <> ys}
      in f <> x <> xs;
  -let-flatten-lr
    ctx = (let G in let {xs = [.]} in f <> x <> xs)
    G1=let {ys = repeat x}
    G2=let {g =[0,0]= (\a. \as . a : as)}
    M=(g <> x <> ys);
  <~> let {xs = let { ys = repeat x
                    , g =[0,0]= (\a. \as . a : as)}
                in g <> x <> ys}
      in f <> x <> xs;
  -let-flatten-rl
    ctx = (let G in let {xs = [.]} in f <> x <> xs)
    G1=let {g =[0,0]= (\a. \as . a : as)}
    G2=let {ys = repeat x}
    M=(g <> x <> ys);
  <~> let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let { ys = repeat x} in g <> x <> ys}
      in f <> x <> xs;
}
qed;
{-
This would be the induction step if induction was implemented, but now
it is in comments and there are two separate proofs instead.

  <~> let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let { ys = repeat^n x} in g <> x <> ys}
      in f <> x <> xs;

-ih
  ctx = (let G in let {xs = let {g =[0,0]= (\a. \as . a : as)}
                            in [.]}
                  in f <> x <> xs)
  f=g
  x=x
  |~> let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let {ys = x : ys} in g <> x <> ys}
      in f <> x <> xs;
-}

-- inductive case (after induction)
proposition: G free(x f) |-
      let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let {ys = x : ys} in g <> x <> ys}
      in f <> x <> xs
      |~> let {xs = x : xs} in f <> x <> xs;
proof: -simple -single{
  -unfold-5-lr
    ctx=(let G in let {xs = [.]} in f <> x <> xs)
    G= let {}
    x=g
    V=(\a. \as . a : as)
    C=(let {ys = x : ys} in [.] <> x <> ys);
  <~> let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let {ys = x : ys} in (\b. \bs . b : bs) <> x <> ys}
      in f <> x <> xs;
  -balloon-reduction-lr
    ctx= (let G in let {xs = let {g =[0,0]= (\a. \as . a : as)}
                  in let {ys = x : ys} in [.] <> ys}
        in f <> x <> xs)
    x=b
    M=(\bs . b : bs)
    y=x;
  <~> let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let {ys = x : ys} in (\bs . x : bs) <> ys}
      in f <> x <> xs;
  -balloon-reduction-lr
    ctx=(let G in let {xs = let {g =[0,0]= (\a. \as . a : as)}
                            in let {ys = x : ys} in [.]}
                  in f <> x <> xs)
    M=(x : bs)
    x=bs
    y=ys;
  <~> let {xs = let {g =[0,0]= (\a. \as . a : as)}
                in let {ys = x : ys} in x : ys}
      in f <> x <> xs;
  -gc-lr
    ctx=(let G in  let {xs = [.]}
                   in f <> x <> xs)
    G1 = let {}
    G2 = let {g =[0,0]= (\a. \as . a : as)}
    X={}
    M=(let {ys = x : ys} in x : ys);
  <~> let {xs = {}d^(let {}
                     in let {ys = x : ys} in x : ys)}
      in f <> x <> xs;
  -dummy-ref-algebra-5-lr
    ctx=(let G in let {xs = [.]}
                  in f <> x <> xs)
    M=(let {} in let {ys = x : ys} in x : ys);
  <~> let {xs = (let {} in let {ys = x : ys} in x : ys)}
      in f <> x <> xs;
  -empty-let-lr
    ctx = (let G in let {xs = [.]}
                    in f <> x <> xs)
    N=(let {ys = x : ys} in x : ys);
  <~> let {xs = let {ys = x : ys} in x : ys}
      in f <> x <> xs;
  -- End of extra work needed because general metavariable M is not
  -- implemented.
  -value-merge'
    ctx=(let G in [.])
    G=let {}
    x=xs
    y=ys
    V=(x:ys)
    M=(f <> x <> xs);
  |~> let {xs = x : xs} in f <> x <> xs;
} qed;

-- for repeat
-dummy-ref-algebra-8:            {X}d^M |~> M;
-@-rules-3:                        R[@] <~> {FV(R)}d^@;
-@-rules-2:     let G {x = {X}d^@} in N |~> let G {x = M} in N
  if FV(M) subsetof X union {x};
-spike-algebra-zero-stack-spike: [0]s^M <~> M;
-reduction:                    [w]^R[V] <~> [w]s^{X}d^N
  if (R[V] ~~> N) && (FV(R[V]) = FV({X}d^N));
-dummy-ref-algebra-5:             {}d^M <~> M;
-spike-algebra-13:               [w]s^M |~> M;
-let-elim:       let {x =[v,w]= M} in x <~> [w]h^M if not x in FV(M);
-let-R:               let G in [w]^R[M] <~> [w]^R[let G in M]
  if dom G subsetof FV(M);
-let-flatten:     let G1 in let G2 in M <~> let G1 G2 in M
  if dom G2 subsetof FV(M);
-unfold-5:  let G {x =[0,0]= V} in C[x] <~> let G {x =[0,0]= V} in C[V];
-value-merge': let G {x = let {y = V} in V} in M
           |~> let G {x = V[x/y]} in M;

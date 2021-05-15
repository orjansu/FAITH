bindings {}

proposition: |-
    let {a = let { b = 1
                 , c = 2}
                in b + c
        ,d = let { e = 3
                 , f = 4}
             in e + f} in a
<~> let{ a = let {c = 2}
             in let {b = 1}
                in b + c
       , d = let { e = 3
                 , f = 4}
             in e + f} in a;
proof: -simple -single{
  -let-flatten-rl
    ctx=(let {a = [.],d = let { e = 3
                              , f = 4}
                          in e + f} in a)
    G1=let {c = 2}
    G2=let {b = 1}
    M=(b + c);
  <~>
}
qed;

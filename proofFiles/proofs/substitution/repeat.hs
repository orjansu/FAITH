bindings {
G = {repeat =[0,0]= \x'. let {ys = repeat x'} in x':ys};
}

-- base case
proposition: G free(x f) |- let {xs = {repeat}d^@ x} in f x xs
                        |~> let {xs = x : xs} in f x xs;
proof: -simple -single{
  -dummy-ref-algebra-8
    ctx=(let G in let {xs = [.] x} in f x xs)
    X={repeat}
    M=@;
  |~> let {xs = @ x} in f x xs;
  -@-rules-3-lr
    ctx = (let G in let {xs = [.]} in f x xs)
    R=([.] x);
  <~> let {xs = {x}d^@} in f x xs;
  -@-rules-2
    ctx=(let G in [.])
    G=let {}
    x=xs
    X={x}
    N=(f x xs)
    M=(x:xs);
  |~> let {xs = x : xs} in f x xs;
} qed;
--inductive case (before induction)
proposition: G free(x f) |- let {xs = [0]s^(\x. let {ys = repeat x}
                                                in x : ys) x} in f x xs
                        |~> let {xs = let {ys = repeat x} in x : ys} in f x xs
proof: -simple -single{
  -spike-algebra-zero-stack-spike-lr
    ctx=(let G in let {xs= [.] x} in f x xs)
    M=(\x. let {ys = repeat x} in x : ys)
  <~> let {xs = (\x. let {ys = repeat x} in x : ys) x} in f x xs
}
--inductive case (after induction)
--proposition: G free(x f) |- let {xs = let {ys = x : ys} in x : ys} in f x xs
--                        |~> let {xs = x : xs} in f x xs

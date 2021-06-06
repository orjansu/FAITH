bindings {
G = {head = \a. case a of
                  { b:bs -> b}
    };
}

proposition: G |- let {y = 1, xs = y : xs} in let {z = 2} in head xs
              |~> 1;--let {y = 1, xs = y : xs} in let {z = 2} in head 1;
proof: -simple -single{
  -unfold-3
    ctx = (let G in [.])
    G = let {y = 1}
    x = xs
    v=1
    w=1
    V=(y:xs)
    C= [.];--(let {z = 2} in head [.]);
  <~>
  $
}
qed;

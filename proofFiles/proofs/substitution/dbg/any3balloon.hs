bindings {
}

-- pre-induction
proposition: free(p xs) |-
    let { map_a = \f3 . \l3 . 1} in case (\f3 . \l3 . f3) <> p <> xs of {}
    <~>
    let { map_a = \f3 . \l3 . 1} in case (\l3 . p) <> xs of {};
proof: -simple -single {
  -balloon-reduction-lr
    ctx=(let { map_a = \f3 . \l3 . 1} in case [.] <> xs of {})
    x=f3 y=p
    M=(\l3 . f3);
  <~>
} qed;

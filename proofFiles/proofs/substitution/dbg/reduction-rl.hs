bindings {
}

proposition: free(p xs any_a or) |-
  [1]s^{}d^p
  <~>
  ((\p9 . p9) p);
proof: -simple -single{
-reduction-rl
  ctx = [.]
  w=1
  R=([.] p)
  V=(\p9 . p9)
  N=p
  X={};
<~>
} qed;

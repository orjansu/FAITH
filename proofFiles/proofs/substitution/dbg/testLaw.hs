bindings{}

proposition: free(d) |- (\z.z) d + (\x.x) d + (\y.y) d
                      |~> 1;
proof: -simple -single{
  -test
    ctx= [.]
    M=(\a.a)
    N=(\b.b)
    x=d;
  |~>
}qed;

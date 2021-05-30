bindings{}

proposition: free(x) |- (\b.x) x + (\c.x) x + (\d.x) x
                      |~> 1;
proof: -simple -single{
  -test-2
    ctx= [.]
    C=(\a.[.])
    D=(\b.[.])
    x=x
    y=x;
  |~>
  1;
}qed;

proposition: free(x) |- \a. \b. x |~> 1;
proof: -simple -single{
  -test-3
    ctx = [.]
    C=(\a . [.])
    x=x;
  |~>
}qed;

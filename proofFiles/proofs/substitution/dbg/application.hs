bindings{}

proposition: free(x y) |- (\a. \b. 1) y x =def= (\a. (\b. 1) x) y;
proof: -simple -single{
-alpha-equiv;
=def=
}
qed;
{-
< G , (((\a. \b. 1) x) y), S>
< G , ((\a. \b. 1) x)    , [.] y : S> v
< G , (\a. \b. 1)        , [.] x : [.] y : S> v+w
< G , (\b. 1)            , [.] y : S> v
< G , 1                  , S>

< G , (\a. (\b. M) x) y , S>
< G , (\a. (\b. M) x)   , [.] y : S> v
< G , (\b. M[y/a]) x    , S>
< G , (\b. M)           , [.] x : S> w
< G , M[y/a][x/b]       , S>

(\a. (\b. M) <w> x) <v> y) -> max (w,v)
(\a. \b. M) <w> x <v> y    -> w + v
                              2*max (w,v) =< w + v
            (\ a. \b. M) x y <~> s^((\a. (\b. M) x) y)
[v] ([w] ((\ a. \b. M) x) y) <~> s^((\a. (\b. M) x) y)

< G , (((\a. \b. M) x) y), S>
< G , ((\a. \b. M) x)    , [.] y : S>
< G , (\a. \b. M)        , [.] x : [.] y : S>
< G , (\b. M[x/a])       , [.] y : S>
< G , M[x/a][y/b]        , S>

(\a. (\b. M) <w> x) <v> y)
[v]s^(\b. M) <w> x)
[w]s^[v]s^M

(((\a. \b. 1) x) y)

-}

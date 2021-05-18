bindings {
G = { any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
                       { [] -> s^False
                       , y1:ys1 -> s^(let { z1 = @
                                        , a1 = p1 <> y1
                                        , b1 = {z1}d^(any_a <> p1 <> ys1)}
                                    in or <> a1 <> b1)})
    , foldr_a =[0,0]= \f2 . \ z2 . \l2 .
                      case l2 of
                        { [] -> z2
                        , a2:as2 -> let {t2 = foldr_a <> f2 <> z2 <> as2}
                                    in f2 <> a2 <> t2}
    , map_a =[0,0]= \f3 . \l3 . case l3 of
        { [] -> []
        , a3:as3 -> let { h3 = f3 <> a3
                        , t3 = map_a <> f3 <> as3}
                    in h3:t3
        }
    , or =[0,0]= \a4. \b4. case a4 of
                         { True -> True
                         , False -> b4
                         }
    , false =[0,0]= False
    };
}

-- pre-induction
proposition: G free(p xs) |-
  let { b = map_a <> p <> xs}
  in foldr_a <> or <> false <> b
  <~>
  h^([2] case xs of
           { [] -> s^false
           , b : bs -> s^(let { z = @
                              , ds = {z}d^(let {cs = map_a <> p <> bs}
                                           in foldr_a <> or <> false <> cs)}
                             in let {c = p <> b}
                                in or <> c <> ds)});

proof: -simple -single {
  let {b = map_a <> p <> xs}
  in foldr_a <> or <> false <> b;
  -unfold-5-lr
    ctx = [.]
    G= let { any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
                              { [] -> s^False
                              , y1:ys1 -> s^(let { z1 = @
                                               , a1 = p1 <> y1
                                               , b1 = {z1}d^(any_a <> p1 <> ys1)}
                                           in or <> a1 <> b1)})
           , map_a =[0,0]= \f3 . \l3 . case l3 of
               { [] -> []
               , a3:as3 -> let { h3 = f3 <> a3
                               , t3 = map_a <> f3 <> as3}
                           in h3:t3
               }
           , or =[0,0]= \a4. \b4. case a4 of
                                { True -> True
                                , False -> b4
                                }
           , false =[0,0]= False
           }
    x = foldr_a
    V = (\f5 . \ z5 . \l5 .
           case l5 of
             { [] -> z5
             , a5:as5 -> let {t5 = foldr_a <> f5 <> z5 <> as5}
                         in f5 <> a5 <> t5})
    C = (let { b = map_a <> p <> xs}
         in [.] <> or <> false <> b);
  <~>
  let { b = map_a <> p <> xs}
  in (\f5 . \ z5 . \l5 .
         case l5 of
           { [] -> z5
           , a5:as5 -> let {t5 = foldr_a <> f5 <> z5 <> as5}
                       in f5 <> a5 <> t5}) <> or <> false <> b;
  -balloon-reduction-lr
    ctx = (let G in let { b = map_a <> p <> xs}
                    in [.] <> false <> b)
    M = (\ z5 . \l5 .
           case l5 of
             { [] -> z5
             , a5:as5 -> let {t5 = foldr_a <> f5 <> z5 <> as5}
                         in f5 <> a5 <> t5})
    x=f5 y=or;
  <~>
  let { b = map_a <> p <> xs}
  in (\ z5 . \l5 .
         case l5 of
           { [] -> z5
           , a5:as5 -> let {t5 = foldr_a <> or <> z5 <> as5}
                       in or <> a5 <> t5}) <> false <> b;
  -balloon-reduction-lr
    ctx = (let G in let {b = map_a <> p <> xs}
                    in [.] <> b)
    x=z5 y=false
    M=(\l5 . case l5 of
             { [] -> z5
             , a5:as5 -> let {t5 = foldr_a <> or <> z5 <> as5}
                         in or <> a5 <> t5});
  <~>
  let { b = map_a <> p <> xs}
  in (\l5 . case l5 of
           { [] -> false
           , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                       in or <> a5 <> t5}) <> b;
  -balloon-reduction-lr
    ctx = (let G in let { b = map_a <> p <> xs}
                    in [.])
    x=l5 y = b
    M=(case l5 of
             { [] -> false
             , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                         in or <> a5 <> t5});
  <~>
  let { ys5 = map_a <> p <> xs}
  in (case ys5 of
           { [] -> false
           , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                       in or <> a5 <> t5});
  -let-R-lr
    ctx = (let G in [.])
    G = let {ys5 = map_a <> p <> xs}
    w=1
    R=(case [.] of { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5})
    M=ys5;
  <~> (case (let {ys5 = map_a <> p <> xs} in ys5) of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -let-elim-lr
    x=ys5
    v=1
    w=1
    M=(map_a <> p <> xs)
    ctx=(let G in (case [.] of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}));
  <~> (case h^(map_a <> p <> xs) of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -spike-algebra-2-lr
    ctx=(let G in [.])
    w=1
    R=(case [.] of
                { [] -> false
                , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                            in or <> a5 <> t5})
    v=1
    M=(map_a <> p <> xs);
  <~> h^(case map_a <> p <> xs of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -unfold-5-lr
    ctx= [.]
    G= let { any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
                              { [] -> s^False
                              , y1:ys1 -> s^(let { z1 = @
                                               , a1 = p1 <> y1
                                               , b1 = {z1}d^(any_a <> p1 <> ys1)}
                                           in or <> a1 <> b1)})
           , foldr_a =[0,0]= \f2 . \ z2 . \l2 .
                             case l2 of
                               { [] -> z2
                               , a2:as2 -> let {t2 = foldr_a <> f2 <> z2 <> as2}
                                           in f2 <> a2 <> t2}
           , or =[0,0]= \a4. \b4. case a4 of
                                { True -> True
                                , False -> b4
                                }
           , false =[0,0]= False
           }
    V= (\f3 . \l3 . case l3 of
        { [] -> []
        , a3:as3 -> let { h3 = f3 <> a3
                        , t3 = map_a <> f3 <> as3}
                    in h3:t3})
    x=map_a
    C=(h^(case [.] <> p <> xs of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}));
  <~> h^(case (\f7 . \l7 . case l7 of
                                { [] -> []
                                , a7:as7 -> let { h7 = f7 <> a7
                                                , t7 = map_a <> f7 <> as7}
                                            in h7:t7}) <> p <> xs of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -balloon-reduction-lr
    ctx=(let G in h^(case [.] <> xs of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}))
    x=f7 y=p
    M=(\l8 . case l8 of
               { [] -> []
               , a8:as8 -> let { h8 = f7 <> a8
                               , t8 = map_a <> f7 <> as8}
                           in h8:t8});
  <~> h^(case (\l7 . case l7 of
                          { [] -> []
                          , a7:as7 -> let { h7 = p <> a7
                                          , t7 = map_a <> p <> as7}
                                      in h7:t7}) <> xs of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -balloon-reduction-lr
    ctx=(let G in h^(case [.] of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}))
    x=l7 y=xs
    M=(case l7 of
         { [] -> []
         , a7:as7 -> let { h7 = p <> a7
                         , t7 = map_a <> p <> as7}
                     in h7:t7});
  <~> h^(case case xs of
                          { [] -> []
                          , a7:as7 -> let { h7 = p <> a7
                                          , t7 = map_a <> p <> as7}
                                      in h7:t7} of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -R-case-lr
    ctx= (let G in h^[.])
    R=(case [.] of
                { [] -> false
                , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                            in or <> a5 <> t5})
    w=1
    v=1
    M=xs
    pat_i=patterns [ [], a10:as10 ]
    N_i=terms [ [],  let { h7 = p <> a10
                         , t7 = map_a <> p <> as10}
                     in h7:t7];
  <~> h^ ([2] case xs of
        { [] -> case [] of
                  { [] -> false
                  , a10:as10 -> let {t5 = foldr_a <> or <> false <> as10}
                              in or <> a10 <> t5}
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -reduction-lr
    ctx = (let G in h^ ([2] case xs of
          { [] -> [.]
          , b:bs -> case let { h7 = p <> b
                             , t7 = map_a <> p <> bs}
                         in h7:t7 of
                      { [] -> false
                      , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                  in or <> a9 <> t9}
          }))
    w=1
    R=(case [.] of
              { [] -> false
              , a10:as10 -> let {t5 = foldr_a <> or <> false <> as10}
                          in or <> a10 <> t5})
    V= []
    X={or foldr_a}
    N=false;
  <~> h^ ([2] case xs of
        { [] -> s^{or foldr_a}d^false
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -dummy-ref-algebra-7-rl
    ctx=(let G in h^ ([2] case xs of
          { [] -> s^[.]
          , b:bs -> case let { h7 = p <> b
                             , t7 = map_a <> p <> bs}
                         in h7:t7 of
                      { [] -> false
                      , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                  in or <> a9 <> t9}
          }))
    X={or}
    Y={foldr_a}
    M=false;
  <~> h^ ([2] case xs of
        { [] -> s^{or}d^{foldr_a}d^false
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -dummy-ref-algebra-3-lr
    ctx = [.]
    G= let { any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
                           { [] -> s^False
                           , y1:ys1 -> s^(let { z1 = @
                                            , a1 = p1 <> y1
                                            , b1 = {z1}d^(any_a <> p1 <> ys1)}
                                        in or <> a1 <> b1)})
        , map_a =[0,0]= \f3 . \l3 . case l3 of
            { [] -> []
            , a3:as3 -> let { h3 = f3 <> a3
                            , t3 = map_a <> f3 <> as3}
                        in h3:t3
            }
        , or =[0,0]= \a4. \b4. case a4 of
                             { True -> True
                             , False -> b4
                             }
        , false =[0,0]= False
        }
    x=foldr_a
    w=0
    V= (\f2 . \ z2 . \l2 .
                          case l2 of
                            { [] -> z2
                            , a2:as2 -> let {t2 = foldr_a <> f2 <> z2 <> as2}
                                        in f2 <> a2 <> t2})
    C=( h^ ([2] case xs of
          { [] -> s^{or}d^[.]
          , b:bs -> case let { h7 = p <> b
                             , t7 = map_a <> p <> bs}
                         in h7:t7 of
                      { [] -> false
                      , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                  in or <> a9 <> t9}
          }))
    M=false;
  <~> h^ ([2] case xs of
        { [] -> s^{or}d^{}d^false
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -dummy-ref-algebra-5-lr
  ctx=(let G in h^ ([2] case xs of
        { [] -> s^{or}d^[.]
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        }))
    M=false;
  <~> h^ ([2] case xs of
        { [] -> s^{or}d^false
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -dummy-ref-algebra-3-lr
    ctx= [.]
    G= let { any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
                           { [] -> s^False
                           , y1:ys1 -> s^(let { z1 = @
                                            , a1 = p1 <> y1
                                            , b1 = {z1}d^(any_a <> p1 <> ys1)}
                                        in or <> a1 <> b1)})
        , foldr_a =[0,0]= \f2 . \ z2 . \l2 .
                          case l2 of
                            { [] -> z2
                            , a2:as2 -> let {t2 = foldr_a <> f2 <> z2 <> as2}
                                        in f2 <> a2 <> t2}
        , map_a =[0,0]= \f3 . \l3 . case l3 of
            { [] -> []
            , a3:as3 -> let { h3 = f3 <> a3
                            , t3 = map_a <> f3 <> as3}
                        in h3:t3
            }
        , false =[0,0]= False
        }
    x=or
    w=0
    V=(\a4. \b4. case a4 of
                   { True -> True
                   , False -> b4
                   })
    M=false
    C=(h^ ([2] case xs of
          { [] -> s^[.]
          , b:bs -> case let { h7 = p <> b
                             , t7 = map_a <> p <> bs}
                         in h7:t7 of
                      { [] -> false
                      , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                  in or <> a9 <> t9}
          }));
  <~> h^ ([2] case xs of
        { [] -> s^{}d^false
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -dummy-ref-algebra-5-lr
    ctx=(let G in h^ ([2] case xs of
          { [] -> s^[.]
          , b:bs -> case let { h7 = p <> b
                             , t7 = map_a <> p <> bs}
                         in h7:t7 of
                      { [] -> false
                      , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                  in or <> a9 <> t9}
          }))
    M=false;
  <~> h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> case let { h7 = p <> b
                           , t7 = map_a <> p <> bs}
                       in h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -let-R-rl
    ctx=(let G
         in h^ ([2] case xs of
          { [] -> s^false
          , b:bs -> [.]
          }))
    R=(case [.] of
                { [] -> false
                , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                            in or <> a9 <> t9})
    G=let { h7 = p <> b, t7 = map_a <> p <> bs}
    M=(h7:t7)
    w=1;
  <~> h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> let { h7 = p <> b
                      , t7 = map_a <> p <> bs}
                  in case h7:t7 of
                    { [] -> false
                    , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                                in or <> a9 <> t9}
        });
  -reduction-lr
    ctx=(let G
         in h^ ([2] case xs of
          { [] -> s^false
          , b:bs -> let { h7 = p <> b
                        , t7 = map_a <> p <> bs}
                    in [.]
          }))
    w=1
    R=(case [.] of
      { [] -> false
      , a9:as9 -> let {t9 = foldr_a <> or <> false <> as9}
                  in or <> a9 <> t9})
    V=(h7:t7)
    X={}
    N=(let {t = foldr_a <> or <> false <> t7}
       in or <> h7 <> t);
  <~> h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> let { h7 = p <> b
                      , t7 = map_a <> p <> bs}
                  in s^{}d^(let {t9 = foldr_a <> or <> false <> t7}
                            in or <> h7 <> t9)
        });
  -dummy-ref-algebra-5-lr
    ctx=(let G
         in h^ ([2] case xs of
          { [] -> s^false
          , b:bs -> let { h7 = p <> b
                        , t7 = map_a <> p <> bs}
                    in s^[.]
          }))
    M=(let {t9 = foldr_a <> or <> false <> t7}
              in or <> h7 <> t9);
  <~>  h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> let { h7 = p <> b
                      , t7 = map_a <> p <> bs}
                  in s^(let {t9 = foldr_a <> or <> false <> t7}
                        in or <> h7 <> t9)
        });
  -spike-algebra-3-lr
    ctx=(let G
        in h^ ([2] case xs of
          { [] -> s^false
          , b:bs -> [.]
          }))
    G= let { h7 = p <> b
           , t7 = map_a <> p <> bs}
    v=1
    M=(let {t9 = foldr_a <> or <> false <> t7}
       in or <> h7 <> t9);
  <~> h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> s^(let { h7 = p <> b
                         , t7 = map_a <> p <> bs}
                     in let {t9 = foldr_a <> or <> false <> t7}
                        in or <> h7 <> t9)
        });
  -let-flatten-lr
    ctx = (let G in h^ ([2] case xs of
                      { [] -> s^false
                      , b:bs -> s^[.]
                      }))
    G1 = let { h7 = p <> b, t7 = map_a <> p <> bs}
    G2= let {t9 = foldr_a <> or <> false <> t7}
    M=(or <> h7 <> t9);
  <~> h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> s^(let { c = p <> b
                         , cs = map_a <> p <> bs
                         , ds = foldr_a <> or <> false <> cs}
                     in or <> c <> ds)
        });
  -let-flatten-rl
    ctx=(let G
        in h^ ([2] case xs of
          { [] -> s^false
          , b:bs -> s^[.]
          }))
    G1= let {cs = map_a <> p <> bs, ds = foldr_a <> or <> false <> cs}
    G2= let { c = p <> b}
    M=(or <> c <> ds);
  <~>  h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> s^(let { cs = map_a <> p <> bs
                         , ds = foldr_a <> or <> false <> cs}
                     in let {c = p <> b}
                        in or <> c <> ds)
        });
  -let-let'-lr
    ctx=(let G in h^ ([2] case xs of
                    { [] -> s^false
                    , b:bs -> s^[.]
                    }))
    G1=let {cs = map_a <> p <> bs}
    x=ds
    v=1 w=1
    M=(foldr_a <> or <> false <> cs)
    N=(let {c = p <> b}
       in or <> c <> ds)
    G2=let {z = @};
  <~> h^ ([2] case xs of
        { [] -> s^false
        , b:bs -> s^(let { z = @
                         , ds = {z}d^(let {cs = map_a <> p <> bs}
                                      in foldr_a <> or <> false <> cs)}
                     in let {c = p <> b}
                        in or <> c <> ds)
        });
} qed;

-- post-induction
proposition: G free(p xs) |-
  h^ ([2] case xs of
            { [] -> s^false
            , b:bs -> s^(let { z = @
                             , ds = {z}d^(any_a <> p <> bs)}
                         in let {c = p <> b}
                            in or <> c <> ds)
            })
  <~>
  any_a <> p <> xs;
proof: -simple -single {
  h^ ([2] case xs of
            { [] -> s^false
            , b:bs -> s^(let { z = @
                             , ds = {z}d^(any_a <> p <> bs)}
                         in let {c = p <> b}
                            in or <> c <> ds)
            });
  -let-flatten-lr
    ctx=(let G in h^ ([2] case xs of
              { [] -> s^false
              , b:bs -> s^[.]
              }))
    G1=let { z = @, ds = {z}d^(any_a <> p <> bs)}
    G2=let {c = p <> b}
    M=(or <> c <> ds);
  <~> h^ ([2] case xs of
            { [] -> s^false
            , b:bs -> s^(let { z = @
                             , ds = {z}d^(any_a <> p <> bs)
                             , c = p <> b}
                         in or <> c <> ds)
            });
  -unfold-5-lr
    ctx = [.]
    G=let { any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
                           { [] -> s^False
                           , y1:ys1 -> s^(let { z1 = @
                                            , a1 = p1 <> y1
                                            , b1 = {z1}d^(any_a <> p1 <> ys1)}
                                        in or <> a1 <> b1)})
        , foldr_a =[0,0]= \f2 . \ z2 . \l2 .
                          case l2 of
                            { [] -> z2
                            , a2:as2 -> let {t2 = foldr_a <> f2 <> z2 <> as2}
                                        in f2 <> a2 <> t2}
        , map_a =[0,0]= \f3 . \l3 . case l3 of
            { [] -> []
            , a3:as3 -> let { h3 = f3 <> a3
                            , t3 = map_a <> f3 <> as3}
                        in h3:t3
            }
        , or =[0,0]= \a4. \b4. case a4 of
                             { True -> True
                             , False -> b4
                             }
        }
    x=false
    V=False
    C=(h^ ([2] case xs of
              { [] -> s^[.]
              , b:bs -> s^(let { z = @
                               , ds = {z}d^(any_a <> p <> bs)
                               , c = p <> b}
                           in or <> c <> ds)
              }));
  <~> h^ ([2] case xs of
            { [] -> s^False
            , b:bs -> s^(let { z = @
                             , ds = {z}d^(any_a <> p <> bs)
                             , c = p <> b}
                         in or <> c <> ds)
            });
  -reduction-rl
    ctx = (let G in [.])
    w=0
    R=([.] p)
    V=(\p9 . h^ ([2] case xs of
              { [] -> s^False
              , b:bs -> s^(let { z9 = @
                               , ds9 = {z9}d^(any_a <> p9 <> bs)
                               , c9 = p9 <> b}
                           in or <> c9 <> ds9)
              }))
    N=((\p8 . h^ ([2] case xs of
              { [] -> s^False
              , b8:bs8 -> s^(let { z8 = @
                               , ds8 = {z8}d^(any_a <> p8 <> bs8)
                               , c8 = p8 <> b8}
                           in or <> c8 <> ds8)
              })) p)
    X={};
  <~> [0]s^{}d^((\p9 . h^ ([2] case xs of
            { [] -> s^False
            , b:bs -> s^(let { z = @
                             , ds = {z}d^(any_a <> p9 <> bs)
                             , c = p9 <> b}
                         in or <> c <> ds)
            })) <> p);
            $
} qed;
--any_a =[0,0]= \p1. \xs1. h^([2]case xs1 of
--                       { [] -> s^False
--                       , y1:ys1 -> s^(let { z1 = @
--                                        , a1 = p1 <> y1
--                                        , b1 = {z1}d^(any_a <> p1 <> ys1)}
--                                    in or <> a1 <> b1)})

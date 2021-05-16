bindings {
G = { any_a =[0,0]= \p1. \xs1. [2]h^(case xs1 of
                       { [] -> s^False
                       , y1:ys1 -> s^(let { z1 = @
                                        , a1 = p1 <> y1
                                        , b1 = {z1}d^(any_a <> p1 <> y1 <> ys1)}
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
    };
}

-- pre-induction
proposition: G free(p xs) |-
  let { a = False
      , b = map_a <> p <> xs}
  in foldr_a <> or <> a <> b
  <~>
  let {false = False} in
  h^(case (case xs of
            { [] -> []
            , b:bs -> let { h6 = p <> b
                          , t6 = map_a <> p <> bs}
                      in h6:t6
            }) of
      { [] -> false
      , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                  in or <> a5 <> t5});
  --[1]h^([2] case xs of
  --           { [] -> s^False
  --           , b : bs -> [1]s^(let { z = @ --   foldr_a^n
  --                                 , false = False
  --                                 , mappbs = map_a <> p <> bs
  --                                 , ds = {z}d^foldr_a <> false <> mappbs}
  --                             in let {c = p <> b}
  --                                in or <> c <> ds)});
proof: -simple -single {
  let { a = False
      , b = map_a <> p <> xs}
  in foldr_a <> or <> a <> b;
  -unfold-5-lr
    ctx = [.]
    G= let { any_a =[0,0]= \p1. \xs1. [2]h^(case xs1 of
                              { [] -> s^False
                              , y1:ys1 -> s^(let { z1 = @
                                               , a1 = p1 <> y1
                                               , b1 = {z1}d^(any_a <> p1 <> y1 <> ys1)}
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
           }
    x = foldr_a
    V = (\f5 . \ z5 . \l5 .
           case l5 of
             { [] -> z5
             , a5:as5 -> let {t5 = foldr_a <> f5 <> z5 <> as5}
                         in f5 <> a5 <> t5})
    C = (let { a = False
             , b = map_a <> p <> xs}
         in [.] <> or <> a <> b);
  <~>
  let { a = False
      , b = map_a <> p <> xs}
  in (\f5 . \ z5 . \l5 .
         case l5 of
           { [] -> z5
           , a5:as5 -> let {t5 = foldr_a <> f5 <> z5 <> as5}
                       in f5 <> a5 <> t5}) <> or <> a <> b;
  -balloon-reduction-lr
    ctx = (let G in let { a = False
                        , b = map_a <> p <> xs}
                    in [.] <> a <> b)
    M = (\ z5 . \l5 .
           case l5 of
             { [] -> z5
             , a5:as5 -> let {t5 = foldr_a <> f5 <> z5 <> as5}
                         in f5 <> a5 <> t5})
    x=f5 y=or;
  <~>
  let { a = False
      , b = map_a <> p <> xs}
  in (\ z5 . \l5 .
         case l5 of
           { [] -> z5
           , a5:as5 -> let {t5 = foldr_a <> or <> z5 <> as5}
                       in or <> a5 <> t5}) <> a <> b;
  -balloon-reduction-lr
    ctx = (let G in let { a = False
                        , b = map_a <> p <> xs}
                    in [.] <> b)
    x=z5 y=a
    M=(\l5 . case l5 of
             { [] -> z5
             , a5:as5 -> let {t5 = foldr_a <> or <> z5 <> as5}
                         in or <> a5 <> t5});
  <~>
  let { a = False
      , b = map_a <> p <> xs}
  in (\l5 . case l5 of
           { [] -> a
           , a5:as5 -> let {t5 = foldr_a <> or <> a <> as5}
                       in or <> a5 <> t5}) <> b;
  -balloon-reduction-lr
    ctx = (let G in let { a = False
                         , b = map_a <> p <> xs}
                    in [.])
    x=l5 y = b
    M=(case l5 of
             { [] -> a
             , a5:as5 -> let {t5 = foldr_a <> or <> a <> as5}
                         in or <> a5 <> t5});
  <~>
  let { false = False
      , ys5 = map_a <> p <> xs}
  in (case ys5 of
           { [] -> false
           , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                       in or <> a5 <> t5});
  -- extra step needed because the proof doesn't treat false as a constructor,
  -- but a variable.
  -let-flatten-rl
    G1 = let {false = False}
    G2 = let {ys5 = map_a <> p <> xs}
    M = (case ys5 of
             { [] -> false
             , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                         in or <> a5 <> t5})
    ctx = (let G in [.]);
    <~>
    let { false = False}
    in let {ys5 = map_a <> p <> xs}
       in (case ys5 of
                { [] -> false
                , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                            in or <> a5 <> t5});
  -let-R-lr
    ctx = (let G in let {false = False} in [.])
    G = let {ys5 = map_a <> p <> xs}
    w=1
    R=(case [.] of { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5})
    M=ys5;
  <~> let { false = False}
      in (case (let {ys5 = map_a <> p <> xs} in ys5) of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -let-elim-lr
    x=ys5
    v=1
    w=1
    M=(map_a <> p <> xs)
    ctx=(let G in let { false = False}
        in (case [.] of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}));
  <~> let { false = False}
      in (case h^(map_a <> p <> xs) of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -spike-algebra-2-lr
    ctx=(let G in let { false = False}
                  in [.])
    w=1
    R=(case [.] of
                { [] -> false
                , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                            in or <> a5 <> t5})
    v=1
    M=(map_a <> p <> xs);
  <~> let { false = False}
      in h^(case map_a <> p <> xs of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -unfold-5-lr
    ctx= [.]
    G= let { any_a =[0,0]= \p1. \xs1. [2]h^(case xs1 of
                              { [] -> s^False
                              , y1:ys1 -> s^(let { z1 = @
                                               , a1 = p1 <> y1
                                               , b1 = {z1}d^(any_a <> p1 <> y1 <> ys1)}
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
           }
    V= (\f3 . \l3 . case l3 of
        { [] -> []
        , a3:as3 -> let { h3 = f3 <> a3
                        , t3 = map_a <> f3 <> as3}
                    in h3:t3})
    x=map_a
    C=(let { false = False}
        in h^(case [.] <> p <> xs of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}));
  <~> let { false = False}
      in h^(case (\f3 . \l3 . case l3 of
                                { [] -> []
                                , a3:as3 -> let { h3 = f3 <> a3
                                                , t3 = map_a <> f3 <> as3}
                                            in h3:t3}) <> p <> xs of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  -balloon-reduction-lr
    ctx=(let G in let { false = False}
        in h^(case [.] <> xs of
                    { [] -> false
                    , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                                in or <> a5 <> t5}))
    x=f3 y=p
    M=(\l3 . case l3 of
               { [] -> []
               , a3:as3 -> let { h3 = f3 <> a3
                               , t3 = map_a <> f3 <> as3}
                           in h3:t3});
  <~> let { false = False}
      in h^(case (\l3 . case l3 of
                          { [] -> []
                          , a3:as3 -> let { h3 = p <> a3
                                          , t3 = map_a <> p <> as3}
                                      in h3:t3}) <> xs of
                  { [] -> false
                  , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
                              in or <> a5 <> t5});
  $
} qed;

--     let {false = False} in
--     h^case (case xs of
--               { [] -> []
--               , b:bs -> let { h6 = p <> b
--                             , t6 = map_a <> p <> bs}
--                         in h6:t6
--               }) of
--         { [] -> false
--         , a5:as5 -> let {t5 = foldr_a <> or <> false <> as5}
--                     in or <> a5 <> t5}

---- post-induction
--proposition: G free(p xs) |-
--  [1]h^[2] case xs of
--             [] -> s^False
--             b : bs -> [1] let { z = @
--                               , ds = {z}d^(any_a <> p <> bs}
--                           in let {c = p <> b}
--                              in or <> c <> ds
--  <~>
--  any_a <> p <> xs;
--proof: -simple -single {
--
--} qed;

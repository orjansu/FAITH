bindings {
G = { or = \a. \b. case a of
                     { True -> True
                     , False -> b
                     }
    };
}

-- Add gadgets
proposition: G free(f)|-
  let {any = \p. \xs. case xs of
            { [] -> False
            , y:ys -> let { py = p y
                          , anypys = any p y ys}
                      in or py anypys}}
  in f any
   <~~>
  let {any = \p. \xs. [2]h^(case xs of
                   { [] -> s^False
                   , y:ys -> s^(let { z = @
                                    , py = p <> y
                                    , anypys = {z}d^(any <> p <> y <> ys)}
                                in or <> py <> anypys)})
  } in f any;
proof: -simple -single{
  -heap-spike-intro-lr ctx=(let G in (let {any = \p. \xs. [.] } in f any))
                       M= (case xs of
                                 { [] -> False
                                 , y:ys -> let { py = p y
                                               , anypys = any p y ys}
                                           in or py anypys})
                       w=2;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                      { [] -> False
                      , y:ys -> let { py = p y
                                    , anypys = any p y ys}
                                in or py anypys})
       } in f any;
  -stack-spike-intro-lr
    ctx = (let G in let {any = \p. \xs. [2]h^(case xs of
                      { [] -> False
                      , y:ys -> [.]}) } in f any)
    M=(let { py = p y
                  , anypys = any p y ys}
              in or py anypys)
    w=1;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> False
                        , y:ys -> s^(let { py = p y
                                         , anypys = any p y ys}
                                  in or py anypys)})
       } in f any;
  -stack-spike-intro-lr
    ctx = (let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> [.]
                          , y:ys -> s^(let { py = p y
                                           , anypys = any p y ys}
                                    in or py anypys)})
                    } in f any)
    M=False
    w=1;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { py = p y
                                         , anypys = any p y ys}
                                  in or py anypys)})
       } in f any ;
  -balloon-intro-untyped-lr
    ctx = (let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^(let { py = [.]
                                           , anypys = any p y ys}
                                    in or py anypys)})
                    } in f any)
    M=p x=y;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { py = p <> y
                                         , anypys = any p y ys}
                                  in or py anypys)}) } in f any;
  -balloon-intro-untyped-lr
    ctx=(let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^(let { py = p <> y
                                           , anypys = [.] y ys}
                                    in or py anypys)}) } in f any)
    M=any x=p;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { py = p <> y
                                         , anypys = any <> p y ys}
                                  in or py anypys)}) } in f any;
  -balloon-intro-untyped-lr
    ctx=(let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^(let { py = p <> y
                                           , anypys = [.] ys}
                                    in or py anypys)}) } in f any)
    M=(any <> p) x=y;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { py = p <> y
                                         , anypys = any <> p <> y ys}
                                     in or py anypys)}) } in f any;
  -balloon-intro-untyped-lr
    ctx=(let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^(let { py = p <> y
                                           , anypys = [.]}
                                       in or py anypys)}) } in f any)
    M=(any <> p <> y) x=ys;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { py = p <> y
                                         , anypys = any <> p <> y <> ys}
                                     in or py anypys)}) } in f any;
  -let-flatten-rl
    ctx=(let G in let {any = \p. \xs. [2]h^(case xs of
                                   { [] -> s^False
                                   , y:ys -> s^([.])}) } in f any)
    G1=let {anypys = any <> p <> y <> ys}
    G2=let {py = p<> y}
    M=(or py anypys);
  <~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let {anypys = any <> p <> y <> ys}
                                     in let {py = p <> y}
                                        in or py anypys)}) } in f any;
  -dummy-bind-intro-lr
    ctx=(let G in let {any = \p. \xs. [2]h^(case xs of
                                   { [] -> s^False
                                   , y:ys -> s^([.])}) } in f any)
    x=anypys
    M=(any <> p <> y <> ys)
    N=(let {py = p <> y}
       in or py anypys)
    z=z;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { z=@
                                         , anypys = {z}d^(any <> p <> y <> ys)}
                                     in let {py = p <> y}
                                        in or py anypys)}) } in f any;
  -let-flatten-lr
    ctx= (let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^([.])}) } in f any)
    G1=let { z=@, anypys = {z}d^(any <> p <> y <> ys)}
    G2=let {py = p <> y}
    M=(or py anypys);
  <~>  let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { z=@
                                         , anypys = {z}d^(any <> p <> y <> ys)
                                         , py = p <> y}
                                     in or py anypys)}) } in f any;
  -balloon-intro-untyped-lr
    ctx = (let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^(let { z=@
                                           , py = p <> y
                                           , anypys = {z}d^(any <> p <> y <> ys)}
                                       in [.] anypys)}) } in f any)
    M=or x=py;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { z=@
                                         , py = p <> y
                                         , anypys = {z}d^(any <> p <> y <> ys)}
                                     in or <> py anypys)}) } in f any;
  -balloon-intro-untyped-lr
    ctx = (let G in let {any = \p. \xs. [2]h^(case xs of
                          { [] -> s^False
                          , y:ys -> s^(let { z=@
                                           , py = p <> y
                                           , anypys = {z}d^(any <> p <> y <> ys)}
                                       in [.])}) } in f any)
    M=(or <> py) x=anypys;
  <~~> let {any = \p. \xs. [2]h^(case xs of
                        { [] -> s^False
                        , y:ys -> s^(let { z=@
                                         , py = p <> y
                                         , anypys = {z}d^(any <> p <> y <> ys)}
                                     in or <> py <> anypys)}) } in f any;
  }
  qed;

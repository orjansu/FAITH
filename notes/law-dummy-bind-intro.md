I can't use let-flatten twice because of the sidecondition. Let flatten is
`-let-flatten: let G1 in let G2 in M <~> let G1 G2 in M
  if dom G2 subsetof FV(M);`
and dummy-bind-intro is
`-dummy-bind-intro: let {x = M} in N <~~> let {z = @, x = {z}d^M} in N
  if z is fresh;`
In the case study 2, you have the subterm
`let { py = p <> y
     , anypys = any' <> p <> y <> ys}
in or <> py <> anypys`
that should be transfered to
`let { z = @
     , py = p <> y
     , anypys = {z}d^(any' <> p <> y <> ys)}
in or <> py <> anypys`
As established, you can't use the `-dummy-bind-intro` directly, and if you try to use let-flatten twice, it goes
`-let-flatten-rl
  ctx=[.]
  G1=let {py = p <> y}
  G2=let{anypys = any' <> p <> y <> ys}
  M=(or py anypys);`
`<~> let { py = p <> y}
     in let {anypys = any' <> p <> y <> ys}
        in or py anypys;`
(OK)
`-dummy-bind-intro-lr
  ctx = (let { py = p <> y}
         in [.])
  x=anypys
  M=(any' <> p <> y <> ys)
  z=z
  N=(or py anypys);`
`<~~> let { py = p <> y}
      in let { z=@
             , anypys = {z}d^(any' <> p <> y <> ys)}
         in or py anypys`
(OK)
`-let-flatten-lr
  ctx=[.]
  G1=let {py = p <> y}
  G2=let {z=@, anypys = {z}d^(any' <> p <> y <> ys)}
  M=(or py anypys);`
Should be
`<~~> let { z=@
          , py = p <> y
          , anypys = {z}d^(any' <> p <> y <> ys)}
      in or py anypys`
but it doesn't work because the sidecondition
`dom G2 subsetof FV(M)`
doesn't hold because
`{z, anypys}` is not a subset of `{or, py, anypys}`
because of the dummy reference `z`.

Therefore, I think the bore general version of `-dummy-bind-intro` is needed, that includes that there may be other bindings;
`-dummy-bind-intro-G: let G {x = M} in N <~~> let G {z = @, x = {z}d^M} in N
  if z is fresh;`
I don't see how the proof would change.

another solution is to add a more general version of the `-let-flatten` without the sidecondition. I think the side condition is there because if there was mutual recursion between `G1` and `G2`, the

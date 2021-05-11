G = {repeat =[0,0]= \x. (let {ys = repeat x} in (x:ys))}

free (x f) let {xs = repeat x} in f x xs
      <~~> let { x = x : xs } in f x xs
--base case is the same
--inductive case
let G in let {xs = repeat^(n+1) x} in f x xs
...
let {xs = let {ys = repeat^n x} in x : ys} in f x xs
...?...
let {xs = let {ys = repeat^n x} in g x ys
     g = \a. \as. a : as} in f x xs
...?...
let {xs = let G in let {ys = repeat^n x} in g x ys
-ih
      ctx= let {xs = [.]
               g = \a. \as. a : as} in f x xs
      G=G --liksom
      f=g
      x=x
|~> let { xs = let G in let { ys = x : ys } in g x ys
        , g = \a. \as. a : as} in f x xs
...?...
let G in let { xs = let G in let { ys = x : ys } in x:ys} in f x xs
-value-merge'
let G in let { xs = x : xs } in f x xs

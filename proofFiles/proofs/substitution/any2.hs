bindings {
G = { any_a =[0,0]= 1
    , foldr_a =[0,0]= 1
    , map_a =[0,0]= 1
    , or =[0,0]= 1};
}

proposition: G free(p xs) |-
  {any_a}d^@ <> p <> xs
  <~>
  let { a = False
      , b = map_a <> p <> xs}
  in {foldr_a}d^@ <> or <> a <> b;
proof: -simple -single {
  {any_a}d^@ <> p <> xs
  ...
  
  --{any_a}d^([0]s^{a}d^(\a. @ <> a)) <> p <> xs



  [0]^(({any_a}d^[0]^(@ p)) xs)

} qed;

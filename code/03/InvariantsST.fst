module InvariantsST

open FStar.ST

let main() : St unit =
  let r = alloc #nat 0 in
  r := 1;
  r := 2
(*   r := -2 -- expected type Prims.nat; got type Prims.int *)

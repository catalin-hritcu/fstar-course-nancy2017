module SimpleLogMST

open Preorder
open Heapx
open STx
open MRefx
open FStar.List.Tot

let subset' (#a:eqtype) (l1:list a) (l2:list a)
  = (forall x. x `mem` l1 ==> x `mem` l2)
let subset (#a:eqtype) : Tot (preorder (list a)) = subset'

let lref = mref (list int) subset

let add_to_log (r:lref) (v:int) : ST unit (requires (fun _ -> True))
                                     (ensures (fun _ _ h -> v `mem` (sel h r))) =
  r := (v :: !r)

assume val complex_procedure (r:lref) : St unit

let main() : St unit =
  let r = alloc (subset #int) [] in
  add_to_log r 42;
  witness r (fun xs -> 42 `mem` xs);
  assert (token r (fun xs -> 42 `mem` xs));
  complex_procedure r;
  assert (token r (fun xs -> 42 `mem` xs));
  recall r (fun xs -> 42 `mem` xs);
  let xs = !r in
  assert (42 `mem` xs)

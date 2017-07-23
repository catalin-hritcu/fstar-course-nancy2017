module Blah

open Preorder
open Heapx
open STx
open MRefx

val evolve : x:int -> Tot (preorder int)
let evolve x = trivial_preorder int

(* let y = evolve 1 2 3 *)

(* fails *)
val write : r:(STx.mref Prims.int (evolve 1)) -> STx.ST Prims.unit
  (fun h -> evolve 1 (Heapx.sel h r) 42)
  (fun h0 x h1 ->
      evolve 1 (Heapx.sel h0 r) 42 /\ Heapx.contains h0 r /\ h1 == Heapx.upd h0 r 42)
let write (r:mref int (evolve 1)) = r := 42

(* fails *)
(* let write2 (r:mref int (evolve 2)) = STx.op_Colon_Equals r 42 *)

(* fails *)
(* let write3 (r:mref int (evolve 3)) = STx.write r 42 *)

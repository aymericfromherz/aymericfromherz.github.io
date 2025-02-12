module FactorialST

open FStar.Heap
open FStar.ST
open FStar.Mul

val factorial : nat -> Tot nat
let rec factorial n =
  if n = 0 then 1 else n * factorial (n - 1)

// TODO: Specify and implement factorial_st so that reference [r] contains
// factorial n after execution
val factorial_st : n: nat -> r:ref nat ->
                                  ST unit (requires (fun h0      -> True))
                                          (ensures  (fun h0 _ h1 -> sel h1 r == factorial n))
let rec factorial_st n r =
  if n = 0 then r := 1
  else (
    factorial_st (n-1) r;
    let cur = !r in
    r := cur * n
  )

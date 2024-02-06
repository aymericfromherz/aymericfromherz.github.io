module FactorialST

open FStar.Heap
open FStar.ST
open FStar.Mul

val factorial : nat -> Tot nat
let rec factorial x =
  if x = 0 then 1 else x * factorial (x - 1)

// TODO: Specify and implement factorial_st so that reference [r] contains
// factorial n after execution
val factorial_st : n: nat -> r:ref nat ->
                                  ST unit (requires (fun h0      -> True))
                                          (ensures  (fun h0 _ h1 -> True))
let rec factorial_st n r =
  admit()

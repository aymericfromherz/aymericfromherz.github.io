module SumST

open FStar.Ref
open FStar.Mul

let sum_tot (n:nat) = ((n+1) * n) / 2


// TODO: Expand this spec so that sum_st typechecks
let rec sum_st' (r:ref nat) (n:nat)
  : ST unit (requires (fun _ -> True))
            (ensures  (fun _ _ _ -> True))

= if n > 0 then (r := !r + n;
                 sum_st' r (n - 1))


let sum_st (n:nat)
  : ST nat (requires (fun _ -> True))
         (ensures  (fun h0 x h1 -> x == sum_tot n /\
                                     modifies !{} h0 h1))
= let r = alloc 0 in
  sum_st' r n;
  !r

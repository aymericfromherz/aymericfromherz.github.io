module Calc

open FStar.Mul

#reset-options "--z3rlimit 50"

let rec pow2 (x: nat) : Tot pos =
  match x with
  | 0 -> 1
  | _ -> 2 * (pow2 (x - 1))

// BEGIN: Basic math lemmas
assume val distributivity_add_left: a:int -> b:int -> c:int -> Lemma ((a + b) * c = a * c + b * c)

assume val distributivity_add_right: a:int -> b:int -> c:int -> Lemma (a * (b + c) = a * b + a * c)

assume val paren_mul_right: a:int -> b:int -> c:int -> Lemma (a * b * c = a * (b * c))

assume val pow2_plus: n:nat -> m:nat -> Lemma (pow2 n * pow2 m = pow2 (n + m))

assume val swap_mul: a:int -> b:int -> Lemma (a * b = b * a)

assume val euclidean_division_definition: a:int -> b:nonzero ->
  Lemma (a = (a / b) * b + a % b)
// END: Basic math lemmas


val lemma_distr_pow (a b:int) (c d:nat) : Lemma ((a + b * pow2 c) * pow2 d = a * pow2 d + b * pow2 (c + d))
let lemma_distr_pow a b c d =
  calc (==) {
    (a + b * pow2 c) * pow2 d;
    (==) { distributivity_add_left a (b * pow2 c) (pow2 d) }
    a * pow2 d + b * pow2 c * pow2 d;
    (==) { paren_mul_right b (pow2 c) (pow2 d); pow2_plus c d }
    a * pow2 d + b * pow2 (c + d);
  }

val lemma_distr_pow_pow (a:int) (b:nat) (c:int) (d e:nat) :
  Lemma ((a * pow2 b + c * pow2 d) * pow2 e = a * pow2 (b + e) + c * pow2 (d + e))
let lemma_distr_pow_pow a b c d e =
  calc (==) {
    (a * pow2 b + c * pow2 d) * pow2 e;
    (==) { lemma_distr_pow (a * pow2 b) c d e }
    a * pow2 b * pow2 e + c * pow2 (d + e);
    (==) { paren_mul_right a (pow2 b) (pow2 e); pow2_plus b e }
    a * pow2 (b + e) + c * pow2 (d + e);
  }


val lemma_as_nat64_horner (r0 r1 r2 r3:int) :
  Lemma (r0 + r1 * pow2 64 + r2 * pow2 128 + r3 * pow2 192 ==
    ((r3 * pow2 64 + r2) * pow2 64 + r1) * pow2 64 + r0)

let lemma_as_nat64_horner r0 r1 r2 r3 =
  calc (==) {
    r0 + pow2 64 * (r1 + pow2 64 * (r2 + pow2 64 * r3));
    (==) { swap_mul (pow2 64) (r1 + pow2 64 * (r2 + pow2 64 * r3)) }
    r0 + (r1 + pow2 64 * (r2 + pow2 64 * r3)) * pow2 64;
    (==) { swap_mul (pow2 64) (r2 + pow2 64 * r3) }
    r0 + (r1 + (r2 + pow2 64 * r3) * pow2 64) * pow2 64;
    (==) { lemma_distr_pow r1 (r2 + pow2 64 * r3) 64 64 }
    r0 + r1 * pow2 64 + (r2 + pow2 64 * r3) * pow2 128;
    (==) { swap_mul (pow2 64) r3 }
    r0 + r1 * pow2 64 + (r2 + r3 * pow2 64) * pow2 128;
    (==) { lemma_distr_pow r2 r3 64 128 }
    r0 + r1 * pow2 64 + r2 * pow2 128 + r3 * pow2 192;
  }


val lemma_distr_eucl_mul (r a:int) (b:pos) : Lemma (r * (a % b) + r * (a / b) * b = r * a)
let lemma_distr_eucl_mul r a b =
  calc (==) {
    r * (a % b) + r * (a / b) * b;
    (==) { paren_mul_right r (a / b) b }
    r * (a % b) + r * ((a / b) * b);
    (==) { distributivity_add_right r (a % b) (a / b * b) }
    r * (a % b + a / b * b);
    (==) { euclidean_division_definition a b }
    r * a;
  }

val lemma_distr_eucl_mul_add (r a c:int) (b:pos) : Lemma (r * (a % b) + r * (a / b + c) * b = r * a + r * c * b)
let lemma_distr_eucl_mul_add r a c b =
  calc (==) {
    r * (a % b) + r * (a / b + c) * b;
    (==) { paren_mul_right r (a / b + c) b }
    r * (a % b) + r * ((a / b + c) * b);
    (==) { distributivity_add_left (a / b) c b }
    r * (a % b) + r * ((a / b * b) + c * b);
    (==) { distributivity_add_right r (a / b * b) (c * b) }
    r * (a % b) + r * (a / b * b) + r * (c * b);
    (==) { paren_mul_right r (a / b) b; paren_mul_right r c b }
    r * (a % b) + r * (a / b) * b + r * c * b;
    (==) { lemma_distr_eucl_mul r a b }
    r * a + r * c * b;
  }

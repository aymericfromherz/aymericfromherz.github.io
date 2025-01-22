module List

open FStar.List.Tot

// TODO: Implement length, append, and prove lemma append_length
val length: #a: Type -> list a -> nat
let rec length (#a: Type) (l: list a) = admit()

val append: #a: Type -> list a -> list a -> list a
let rec append (#a: Type) (l1 l2: list a) = admit()

val append_length (#a:Type) (l1 l2: list a) :
  Lemma (length l1 + length l2 == length (append l1 l2))
let rec append_length (#a: Type) (l1 l2: list a) = admit()


let snoc l h = l @ [h]

//TODO: Implement reverse, and prove the lemmas rev_snoc and rev_involutive
val reverse: #a:Type -> list a -> Tot (list a)
let rec reverse (#a:Type) l = admit()

val rev_snoc: #a:Type -> l:list a -> h:a ->
  Lemma (reverse (snoc l h) == h::reverse l)
let rec rev_snoc (#a:Type) l h = admit()

val rev_involutive: #a:Type -> l:list a -> Lemma (reverse (reverse l) == l)
let rec rev_involutive (#a:Type) l = admit()

module Rev

open FStar.List.Tot

let snoc l h = l @ [h]

//TODO: Implement reverse, and prove the lemmas rev_snoc and rev_involutive
val reverse: #a:Type -> list a -> Tot (list a)
let rec reverse (#a:Type) l = admit()

val rev_snoc: #a:Type -> l:list a -> h:a ->
  Lemma (reverse (snoc l h) == h::reverse l)
let rec rev_snoc (#a:Type) l h = admit()

val rev_involutive: #a:Type -> l:list a -> Lemma (reverse (reverse l) == l)
let rec rev_involutive (#a:Type) l = admit()

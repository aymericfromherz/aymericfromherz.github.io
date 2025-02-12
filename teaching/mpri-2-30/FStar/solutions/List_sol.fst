module List_sol

open FStar.List.Tot

val length: #a: Type -> list a -> nat

let rec length (#a: Type) (l: list a) = match l with
  | [] -> 0
  | hd :: tl -> 1 + length tl

val append: #a: Type -> list a -> list a -> list a
let rec append (#a: Type) (l1 l2: list a) = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: (append tl l2)

val append_length (#a:Type) (l1 l2: list a) :
  Lemma (length l1 + length l2 == length (append l1 l2))
let rec append_length (#a: Type) (l1 l2: list a) = match l1 with
  | [] -> ()
  | hd :: tl -> append_length tl l2

let snoc l h = l @ [h]

val reverse: #a:Type -> list a -> Tot (list a)
let rec reverse (#a:Type) l = match l with
  | [] -> []
  | hd :: tl -> snoc (reverse tl) hd

val rev_snoc: #a:Type -> l:list a -> h:a ->
  Lemma (reverse (snoc l h) == h::reverse l)
let rec rev_snoc (#a:Type) l h = match l with
  | [] -> ()
  | hd :: tl -> rev_snoc tl h

val rev_involutive: #a:Type -> l:list a -> Lemma (reverse (reverse l) == l)
let rec rev_involutive (#a:Type) l = match l with
  | [] -> ()
  | hd :: tl -> rev_involutive tl; rev_snoc (reverse tl) hd

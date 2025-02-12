module Stack_sol

  let stack = list int


val empty : stack
val is_empty : stack -> GTot bool

val push : int -> stack -> stack
val pop : stack -> option stack
val top : stack -> option int
// END: stack_types


  let empty = []
  let is_empty xs = match xs with
                    | [] -> true
                    | x::xs' -> false
  let push x xs = x :: xs
  let pop xs = match xs with
               | [] -> None
               | x::xs' -> Some xs'
  let top xs = match xs with
               | [] -> None
               | x::xs' -> Some x


// BEGIN: stack_lemmas
val lemma_empty_is_empty : unit -> Lemma (is_empty (empty))

val lemma_push_is_empty : s:stack -> i:int ->
                                            Lemma (~(is_empty (push i s)))

val lemma_is_empty_top_some : s:stack{~(is_empty s)} ->
                                                     Lemma (Some? (top s))

val lemma_is_empty_pop_some : s:stack{~(is_empty s)} ->
                                                     Lemma (Some? (pop s))

val lemma_push_top: s:stack -> i:int ->
                                            Lemma (top (push i s) == Some i)

let lemma_push_pop: s:stack -> i:int -> Lemma (pop (push i s) == Some s) = fun s i -> ()

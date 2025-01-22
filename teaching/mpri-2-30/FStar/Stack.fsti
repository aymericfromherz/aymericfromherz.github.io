module Stack

// BEGIN: stack_types
val stack : Type0  (* type of stacks *)

val empty : stack
val is_empty : stack -> GTot bool

val push : int -> stack -> stack
val pop : stack -> option stack
val top : stack -> option int
// END: stack_types

// BEGIN: stack_lemmas
// END: stack_lemmas

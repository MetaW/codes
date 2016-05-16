(*
	content:
	1.
	2.
	3.
	4.

*)



(* first class function *)
(*---------------------------------------------------------*)
(*
	first class function means that functions can be computed, 
	passed, stored, etc. wherever other values can be computed, 
	passed, stored, etc.
*)





(* lexical scope *)
(*---------------------------------------------------------*)
(*
	lexical scope: The body of a function is evaluated in the
	environment where the function is DEFINED, not the 
	environment where the function is CALLED
*)

(* example *)

val x = 1			(* x->1 *)
fun f y = x + y		(* x->1 *)
val x = 2			(* x->2 *)
val y = 3			(* x->2, y->3 *)
val z = f (x + y)	(* z = f 5 = (1 + 5) = 6 *)



(* ---closures--- *)
(*
	we say functions are values, actually a function is a value
	which has two parts:  the code for function and the environment
	when the function was created. So a function is actually a "pair"
	We call this "pair" closures or function closures.
	But we can not directlly access the "pair", what we can do is just
	call the function and this call will uses both parts of the "pair".

	There are two kinds of variables inside a function: bound variable and
	unbound variable(free varialbe), the former get its value from parameter
	and the latter get its value from the environment of its closures. 
*)




















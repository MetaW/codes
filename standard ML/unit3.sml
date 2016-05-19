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
	environment where the function is CALLED.

	Another scope is dynamic scope, it use the environment where
	the function is called while evaluated.
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






(* currying *)
(*--------------------------------------------------------*)
(*
	We know that every function can take only one parameter
	but like many other FP languages, actually we can define
	a function which take more than one params via a syntex sugar 
	called "CURRYING", which transform a function with more than
	one params to many wraped anonymous function and each of them take
	exactlly one param. 

	Lexical scope is essential to this technique working correctly
*)

(* example *)
fun sorted3 x y z = 
	z >= y andalso y >= x

(* the function above is actually a syntex sugar of the next one *)

val sorted3 = 	(* ATTENTION: here we use val instead of fun *)
	fn x =>
		(fn y =>
			(fn z =>
				(z >= y andalso y >= x)))
(* this process is called currying *)

(* sorted3 1 2 3 = (((sorted3 1) 2) 3) *)


(* partial application *)

sorted3 1 		(*   fn: int -> int -> bool *)
sorted3 1 2 	(*   fn: int -> bool *)
sorted3 1 2 3 	(* true: bool *)



(* conclusion on how to pass more than one params to a function *)
(*
	1. we can put all params into a tuple.
		eg: fun g (x,y,z) = ...
	2. we can use the currying 
		eg: val g x y z = ...

	Attention: the second way is better than the first one, cause
	in the second way we can use partial application.
*)




(* Mutation via reference *)
(*
	ML is not a pure FP language, because it support a way
	to mutate a special kind of data: "ref data". In ML, only
	this kind of data type can be mutate via some syntex sugar.

	ref : constructer
	:=  : syntex sugar for change the content of a ref
	!   : syntex sugar for get the content of a ref
*)

val x = ref 123	(* create a ref data: int ref *)
val x1 = x 		(* x1: int ref *)
val x2 = ref 123	(* x2: int ref *)

val y = !x (* get the content of a ref data. y:int *)
val _ = x:= 234	(* change the content of a ref data *)
(*
x  -> ref 234 : int ref
x1 -> ref 234 : int ref
x2 -> ref 123 : int ref
*)

datatype set = S of { insert : int -> set, member : int -> bool, size : unit -> int }




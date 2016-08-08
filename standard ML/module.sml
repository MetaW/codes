(*
	contents:
	1.
	2.
	3.
*)


(* define and use a module *)
(*---------------------------------------------------*)
(*
	module is a way of namespace managment.
	It contains a lots of bindings。
	separate bindings into different namespaces and
	using modules to hide bindings and types.


syntex:
	structure ModuleName = struct bindings end
*)

(* define *)
structure MathLib =
	struct
		val pi = 3.1415
		val e = 2.71828

		fun fact n:int =
			case n of
	  		0 => 1
				| _ => n * (fact (n - 1))

		fun double n:int =
			2 * n
	end


(* use *)
(*
	"ModuleName.bindingName" will get the binding value
	defined in the module.
*)
val aa = MathLib.pi
val bb = MathLib.fact 5


(*
	if we want expose the binding into the env,
	we can type expression:
		open ModuleName
	so that we can get access to the bindings defined
	in the module without write the module name.
	BUT this action may introduce unexpected shadowing.
*)
open MathLib

val cc = e
val dd = fact 6


(* signature and hiding *)
(*---------------------------------------------------*)
(*
	signature is the type of a module, it can be genarated
	automatically by type inference,for example the module
	MathLib has a signature(type):

  	sig
    	val pi : real
    	val e : real
    	val fact : int -> int
    	val double : int -> int
  	end

	we can manually define a signature and ascrible it
	to a module like manually define a type for function.

	They let us provide strict interfaces that code outside
	the module must obey.

*)

signature TestModuleSig =
  sig
		type rational
		exception badFraction
		val make_frac : int -> int -> rational
    val add : rational -> rational -> rational
    val toString : rational -> string
  end

(*
	signature just like the interface in java, it defined
	the types and names of functions or values for the module
	with that signature.

	Besides, signature also have the ability to control the
	accessibility of bindings inside a module: if a binding
	of a module is not appears in its signature it is "private"
	and it can only be accessed inside the module.
 *)

structure TestModule :> TestModuleSig =
struct
	datatype rational = Whole of int | Frac of int * int
	exception badFraction
	fun make_frac x y =
	 	Frac (x, y)

	fun add x y =
		case (x,y) of
		  (Frac (a1, b1), Frac (a2, b2)) => Frac ((a1 + a2), (b1 + b2))
		| (_, _) => raise badFraction

	fun toString x =
		case x of
		  Frac (a, b) => (Int.toString a) ^ (Int.toString b)
		| Whole a => Int.toString a

	(* hiddenVal and hiddenFun can only be used inside the module *)
	val hiddenVal = 100

	fun hiddenFun x =
		x + 1

end

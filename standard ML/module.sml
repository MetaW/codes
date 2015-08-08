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
	It contains a lots of bindings

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

*)

signature MathLibSig =
  sig
    val pi : real
    val e : real
    val fact : int -> int
    val double : int -> int
  end

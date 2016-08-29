(*
    contents:
    1.  write types expilicitly
    2.  tuple, list, options, pattern-match
    3.  recusive func
    4.  ref
    5.  anonymous function
    6.  labeled arguments
    7.  optional arguments
    8.  bench_mark test
    9.  module, file
    10. record
    11. 
    12. 
    13. 
    14. 
    15. 

*)


(*---------------------------------------*)
(* 1. write types expilicitly *)
let x:int = 123

let f (g:int->bool) (x:int) (y:int) : int =
    ...






(*---------------------------------------*)
(* 2. tuple, list, options, pattern-match *)

(* tuple & list *)
let a1 = (1, "haha", true, 12.34)

let a2 = [1;2;3;4]
let a3 = [true;false;false]
let a4 = 5::6::[7;8;9]

let a5 = [1;2;3] @ [4;5;6] (* notice : "abcs" ^ "cdsvr" *)






(* option type *)
(* trans partial func to total func *)
type 'a option = None | Some of 'a

let safe_div x y =
    if y = 0 then None else Some (x/y)








(* pattern match *)

(* in bindings *)
let (x,y) = (123,"cdasc")
let a::b = [1;2;3;4]

(* in func params *)
let f (x,y) =
    x + y

let head x::y =
    x

(* as expression *)

match [1;2;3] with
    | [] -> 0
    | x::y -> 100






(*---------------------------------------*)
(* 3. recusive func *)
let rec len l =
    match l with
        | [] -> 0
        | x::y -> 1 + (len y)







(*---------------------------------------*)
(* 4. ref *)
let x = ref 0   (* newref *)
x := !x + 5     (* setref + deref *)







(*---------------------------------------*)
(* 5. anonymous function *)
(* fun just like lambda *)
let f1 =
    fun x -> x + x

let f2 =
    fun x y -> x + y


(* another way *)
(* function like haskell style *)
let f3 =
    function
    | [] -> None
    | x::xl -> Some x








(*---------------------------------------*)
(* 6. labeled arguments *)
let yourInfo =
    fun ~name ~age -> "yourInfo is " ^ name ^ age

let try1 = yourInfo ~name:"wll" ~age:"18"
let try2 = yourInfo ~age:"18" ~name:"wll"
(* labeled arguments is useful when we want to
provide more info about the function's params *)









(*---------------------------------------*)
(* 7. optional arguments *)
let f =
    fun ?x y ->
    match x with
    | None -> y
    | Some i -> i + y

let a1 = f 1 2
let a2 = f 3
(* it is just a useless syntex suger of option type *)
(* equals to *)
let f =
    fun x y ->
    match x with
    | None -> y
    | Some i -> i + y
let a1 = f 1 2
let a2 = None 3








(*---------------------------------------*)
(* 8. bench_mark test: *)
(* in utop: *)

# #require "core_bench";;
# open Core_bench.Std;;

(* create test *)
# let test1 = Bench.Test.create ~name:"test1"
                                (fun () -> ignore (List.fold_left ( + ) 0 [1;2;3;4;5]));;

# let test2 = Bench.Test.create ~name:"test2"
                                (fun () -> ignore (List.fold_left ( * ) 0 [1;2;3;4;5]));;
(* start test *)
# Bench.bench [test1;test2];;

(* get result *)
┌───────┬──────────┬─────────┐
| Name  | Time/Run | mWd/Run |
├───────┼──────────┼─────────┤
│ test1 │ 186.87ns │   2.00w │
│ test2 │ 186.55ns │   2.00w │
└───────┴──────────┴─────────┘









(*---------------------------------------*)
(* 9. module, file *)
(*
    a file will automately become a module, eg: 
        myfile.ml ---> Myfile
    bingings in myfile.ml can be accessed by Myfile.xxx

    the module Myfile may has a interface, defined in myfile.mli
*)
(*
    !!! cyclic dependencies between modules are not allowed, 
    and cyclic dependencies among files are never allowed.
*)
a type definition in .ml will be copied into .mli file,
but if we delete its detail in .mli file, just left:
    eg: type t = Foo | Bar of int
    --->type t
then type will become a abstract type.

(* create a module inside a file (nested module) *)
module name : <signature> = <implementation>

eg:(recommand)
module Moe :
    sig
        type t = Foo | Bar of int
        val x : int
        val f : int -> int
    end
    =
    struct
        type t = Foo | Bar of int
        let x = 123
        let f x = x + 1
    end


or define independently

module type MoeSig =
    sig
        type t = Foo | Bar of int
        val x : int
        val f : int -> int
    end

module Moe : MoeSig = 
    struct
        type t = Foo | Bar of int
        let x = 123
        let f x = x + 1
    end









(*---------------------------------------*)
(* 10. record *)
record can be implemented with ADT easily, but in 
OCaml for speed, it was implemented in another way.

type 'a haha = {
    x1 : int;
    x2 : string;
    f1 : int -> int;
    x3 : 'a option
}

let x = {x1 = 123; x2 = "abc"; f1 = (fun x -> x + 1); x3 = Some 5}
let y = x.f1



(*---------------------------------------*)
11

(*---------------------------------------*)
12

(*---------------------------------------*)
13

(*---------------------------------------*)
14

(*---------------------------------------*)
15

(*---------------------------------------*)
16

(*---------------------------------------*)
17

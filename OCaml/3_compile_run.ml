
open Core.Std

type t = 
    | Foo
    | Bar of int

module Moe1 :
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

module type MoeSig =
    sig
        type t = Foo | Bar of int
        val x : int
        val f : int -> int
    end

module Moe2 : MoeSig = 
    struct
        type t = Foo | Bar of int
        let x = 123
        let f x = x + 1
    end


let rec read_and_accum (accum:float) : float =
    let opStr = In_channel.input_line In_channel.stdin in
    match opStr with
    | None -> accum
    | Some str -> read_and_accum (accum +. (Float.of_string str))


let _ = printf "total: %F\n" (read_and_accum 0.0)


(*
    compile:
    in command line:
    $ corebulid 3_compile_run.native  // this will build into native code
    then a file : 3_compiler_run.native was generated

    run:
    in command line:
    $ ./3_compile_run.native
*)


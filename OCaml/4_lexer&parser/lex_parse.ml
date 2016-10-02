open Core.Std
open Lexing

open Myparser
open Mylexer
open Ast


(* trans a AST to string so that we print it out and 
   to see whether the AST is right or not *)
let rec trans_to_str exp =
    match exp with
    | Const_expr v -> (string_of_int v)
    | Add_expr (exp1, exp2) -> "Add_expr(" ^ (trans_to_str exp1) ^ ", " ^ (trans_to_str exp2) ^ ")"
    | Var_expr str -> "Var(" ^ str ^ ")"
    | Let_expr (str, exp1, exp2) -> "let " ^ str ^ " = " ^ (trans_to_str exp1) ^ " in " ^ (trans_to_str exp2)



(*
types:
    In_channel.input_line stdin : <input_something> -> string option
    Lexing.from_string : string -> Lexing.lexbuf
    Mylexer.read : Lexing.lexbuf
    nt_prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)

*)


let () = 
    match In_channel.input_line stdin with (* read from terminal, we modify it to read from a file *)
    | None -> print_endline "\nGood bye."
    | Some line -> let alexbuf = Lexing.from_string line in
                   try 
                   alexbuf
                   |> Myparser.nt_prog Mylexer.read
                   |> trans_to_str
                   |> print_string
                   with
                   | Mylexer.LexerError str -> print_string str                
                   | Myparser.Error -> print_string ("Oops!!! parser error with char: " ^ (Lexing.lexeme alexbuf) 
                                                     ^ " at: " ^ (Mylexer.error_info alexbuf))


(*
let () =  (* parse the program given directlly in the source file *)
    let line = "let x = 123 in 
                    let y = 234 in
                        (x+y)"
    in
    let alexbuf = Lexing.from_string line in
    try 
    alexbuf
    |> Myparser.nt_prog Mylexer.read
    |> trans_to_str
    |> print_string
    with
    | Mylexer.LexerError str -> print_string str                
    | Myparser.Error -> print_string ("Oops!!! parser error with char: " ^ (Lexing.lexeme alexbuf) 
                                      ^ " at: " ^ (Mylexer.error_info alexbuf))

*)
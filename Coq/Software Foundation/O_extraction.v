(*
可以导出的语言:
  OCaml (the most mature)
  Haskell (which mostly works)
  Scheme (a bit out of date).

以OCaml为例：
*)

Extraction Language Ocaml.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import N_impCEvalFun.

(*
we tell Coq the name of a definition to extract and the 
name of a file to put the extracted code into.
*)



Extraction "evalfun.ml" ceval_step2 ceval_step3 ceval_step.
(*
此时编译这个文件就会产生一个evalfun.ml文件，和一个evalfun.mli文件
*)

(*
Since we've proved that the ceval_step function behaves the 
same as the ceval relation in an appropriate sense, the 
extracted program can be viewed as a certified Imp interpreter. 
*)
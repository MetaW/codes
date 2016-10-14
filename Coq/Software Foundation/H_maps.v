Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.


Inductive id:Type :=
  |Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.






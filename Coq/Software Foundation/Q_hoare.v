(*
  contents:
  1. Assertion
    - Open Scope XX
  2. Hoare Triples
  3.
  4.
  5.
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import H_maps.
Require Import L_imp.


(*
在equiv.v中我们讨论了imp的一些meta property。"meta" in the sense 
that they are properties of the language as a whole, rather 
than of particular programs in the language.

在本章中将讲一个 systematic method for reasoning about the correctness
of PARTICULAR programs in Imp
*)



(* Assertions *)
(*------------------------------------------------------------*)
(*
an assertion is just a family of propositions indexed by a state.
*)
Definition Assertion := state -> Prop.

(*example*)
Module ExAssertions.

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

End ExAssertions.


(*
Given two assertions P and Q, we say that P implies Q, written 
P ->> Q, if, whenever P holds in some state st, Q also holds.
*)
Definition assert_implies (P Q: Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope. 


(* Open Scope XX *)
(*
The hoare_spec_scope annotation here tells Coq that this 
notation is not global but is intended to be used in particular
contexts. The Open Scope tells Coq that this file is one such 
context.
*)

Notation "P <<->> Q" :=
  (P ->> Q ∧ Q <<- P) (at level 80) : hoare_spec_scope.











(* Hoare Triples *)
(*------------------------------------------------------------*)
























(*------------------------------------------------------------*)
(*------------------------------------------------------------*)
(*------------------------------------------------------------*)
(*
  contents:
  1. relation
  2. reflexive relation
  3. Transitive Relations
  4. Symmetric and Antisymmetric Relations

*)

Require Export J_indPrinciples.
(*
Coq 已经定义了relation的含义，将它限定为二元关系。
*)
Definition relation (X: Type) := X -> X -> Prop.


(*
A relation R on a set X is a partial function if, for
every x, there is at most one y such that R x y — i.e., 
R x y1 and R x y2 together imply y1 = y2
*)
Definition partial_function {X: Type} (R: X -> X -> Prop) := 
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.


Theorem le_not_a_partial_function : 
  not (partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros.
  assert (0 = 1) as H0.
    -apply H with (x := 0).
     +apply le_n.
     +apply le_S.
      apply le_n.
    -inversion H0.
Qed.









(* reflexive relation *)
(*
A reflexive relation on a set X is one for which every 
element of X is related to itself.
*)
Definition reflexive_relation {X: Type} (R: X -> X -> Prop) :=
  forall x, R x x.

Theorem le_reflexive : reflexive_relation le.
Proof.
  unfold reflexive_relation.
  intros.
  apply le_n.
Qed.









(* Transitive Relations *)
(*
A relation R is transitive if R a c holds whenever R a b and 
R b c do.
*)
Definition transitive {X: Type} (R: relation X) := 
    forall x y z, R x y -> R y z -> R x z.

Theorem le_trans : transitive le.
Proof.
  unfold transitive.
  intros.
  induction H0.
    -apply H.
    -apply le_S.
     apply IHle.
     apply H.
     Show Proof.
Qed.


Theorem lt_trans : transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros.
Admitted.

Theorem le_Sn_le : forall n m, le (S n) m -> le n m.
Proof.
  intros.
  apply le_trans with (S n).
    -apply le_S.
     apply le_n.
    -apply H.
Qed.










(* Symmetric and Antisymmetric Relations *)














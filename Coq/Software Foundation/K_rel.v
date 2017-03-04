(*
  contents:
  1. relation
  2. reflexive relation
  3. Transitive Relations
  4. Symmetric and Antisymmetric Relations
  5. Equivalence Relations
  6. Partial Orders and Preorders
  7. Reflexive, Transitive Closure

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

Definition symmetric {X: Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> R y x.

Definition antisymmetric {X: Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> R y x -> x = y.


Theorem le_not_symm : antisymmetric le.
Proof.
  unfold antisymmetric.
  intros.
  Admitted.



(* Equivalence Relations *)
Definition equivlence {X:Type} (R: X -> X -> Prop) :=
  reflexive_relation R /\ symmetric R /\ transitive R.




(* Partial Orders and Preorders *)
(*
A relation is a partial order when it's reflexive, 
anti-symmetric, and transitive. In the Coq standard 
library it's called just "order" for short.
*)
Definition order {X: Type} (R: relation X) :=
  reflexive_relation R /\ transitive R /\ antisymmetric R.

(* A preorder is almost like a partial order, 
   but doesn't have to be antisymmetric.
 *)
Definition preorder {X:Type} (R: relation X) :=
  reflexive_relation R /\ transitive R.

Theorem le_order : order le.
Proof.
  unfold order.
  split.
    -apply le_reflexive.
    -split.
      +apply le_trans.
      +apply le_not_symm.
Qed.




(* Reflexive, Transitive Closure *)
(*
The reflexive, transitive closure of a relation R is the smallest
relation that contains R and that is both reflexive and transitive
*)
Inductive clos_refl_trans {X: Type} (R: relation X) : relation X :=
| rt_step : forall x y, R x y -> clos_refl_trans R x y
| rt_refl : forall x, clos_refl_trans R x x
| rt_trans : forall x y z, clos_refl_trans R x y -> 
                           clos_refl_trans R y z ->
                           clos_refl_trans R x z.

(*
BTW:the reflexive and transitive closure of the next_nat 
relation is the le relation.
*)

(*
this definition is nature but not very convenient for 
doing proofs, since the "nondeterminism" of the rt_trans 
rule can sometimes lead to tricky inductions. Here is 
a more useful definition:
*)

Inductive clos_refl_trans_1n {A: Type} (R: relation A) (x: A) : A -> Prop :=
| rt1n_refl : clos_refl_trans_1n R x x
| rt1n_trans (y z: A) : R x y -> clos_refl_trans_1n R y z -> 
                                 clos_refl_trans_1n R x z.




















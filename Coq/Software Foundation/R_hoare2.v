(*
  contents:
  1. Decorated Programs
  2.
  3.
  4.
  5.
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import H_maps.
Require Import L_imp.
Require Import Q_hoare.





(* Decorated Programs *)
(*------------------------------------------------------------*)
(*
The beauty of Hoare Logic is that it is compositional: the 
structure of proofs exactly follows the structure of programs.

a decorated program consists of the program text interleaved with 
assertions (either a single assertion or possibly two assertions 
separated by an implication). To check that a decorated program 
represents a valid proof, we check that each individual command is 
locally consistent with its nearby assertions
*)

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  -apply hoare_while.
   eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, bassn, assn_sub. simpl.
    intros. reflexivity.
  -unfold assert_implies, bassn, assn_sub. simpl.
   intros. inversion H. destruct (st X =? 0) eqn:Hx.
   apply beq_nat_true in Hx. assumption. simpl in H1.
   destruct H1. auto.
Qed.






(*Finding Loop Invariants*)
(*------------------------------------------------------------*)
(*
Once the outermost precondition and postcondition are chosen, 
the only creative part in verifying programs using Hoare Logic is 
finding the right loop invariants.

it must be weak enough to be implied by the loop's precondition
it must be strong enough to imply the program's postcondition
it must be preserved by one iteration of the loop

One way to find an invariant that satisfies these three 
conditions is by using an iterative process: start with a 
"candidate" invariant (a guess or a heuristic choice) and check 
the three conditions above; if any of the checks fails, try to 
use the information that we get from the failure to produce 
another candidate invariant, and repeat the process.

Very often, even if a variable is used in a loop in a read-only 
fashion, it is necessary to add to the loop invariant.
*)

(* exercise *)
Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  not (2 <= x) ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity. 
  simpl. exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros m.
  apply hoare_consequence_pre with 
    (P' := (fun st => parity m = parity (st X))).
  -eapply hoare_consequence_post.
   +apply hoare_while.
    eapply hoare_consequence_pre.
    *apply hoare_asgn.
    *unfold assert_implies, bassn, assn_sub. simpl.
     intros. destruct H. rewrite H. unfold t_update. simpl.
     destruct (st X) eqn:He.
     ++inversion H0.
     ++destruct n. ** inversion H0. **simpl. 
       rewrite <- minus_n_O. auto.
   +unfold assert_implies, bassn, assn_sub. simpl. intros.
    destruct H. rewrite H. destruct (st X) eqn:Hx.
    *simpl. reflexivity.
    *destruct n. ++auto. ++destruct H0. reflexivity.
  -unfold assert_implies, bassn, assn_sub. simpl. intros.
   rewrite H. reflexivity.
Qed.






(*------------------------------------------------------------*)

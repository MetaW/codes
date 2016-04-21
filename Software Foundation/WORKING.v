Require Export poly.

Example trans_eq_example: 
	forall (a b c d e f:nat), [a,b] = [c,d] -> [c,d] = [e,f] -> [a,b] = [e,f].

  intros.
  apply trans_eq with [c,d]. (*没有with时会警告m无法找到匹配的东西，此时我们告诉它用[c,d]匹配*)
  apply H.
  apply H0.
Qed.

Example trans_eq_exercise: 
	forall (n m o p:nat), m = (minustwo o) -> (n+p) = m -> (n+p) = (minustwo o).

  intros.
  apply trans_eq with m. (*同上一个例子*)
  apply H0.
  apply H.
Qed.

Check @eq.

Example and_exercise: 
	forall (n m:nat), n + m = 0 -> n = 0 /\ m = 0.

  intros.
  split.
    -induction n.
      +reflexivity.
      +inversion H.
    -induction m.
      +reflexivity.
      +rewrite <- plus_n_Sm in H.
       inversion H.
Qed.


Lemma and_exercise2 : 
	forall (n m:nat), n = 0/\m = 0 -> n + m = 0.
  
  intros.
  destruct H as [HA HB].
  rewrite HA. rewrite HB.
  simpl. reflexivity.
Qed.



Theorem and_commut : 
	forall (P Q:Prop), P /\ Q -> Q /\ P.

  intros.
  destruct H as [HA HB].
  split.
    -apply HB.
    -apply HA.
Qed.



Theorem and_assoc : 
	forall (P Q R:Prop), P /\ (Q /\ R) -> (P /\ Q) /\ R.

  intros.
  destruct H as [HA [HB HC]].
  split.
    -split. +apply HA. +apply HB.
    -apply HC.
Qed.


Check and.


Lemma or_example : 
	forall (n m:nat), n = 0 \/ m = 0 -> n*m = 0.

  intros.
  destruct H.
    -rewrite H. reflexivity.
    -rewrite H. rewrite <- mult_n_O. reflexivity.
Qed.


Lemma or_intro : 
	forall (A B:Prop), A -> A \/ B.
  
  intros.
  left.
  apply H.
Qed.


Lemma zero_or_succ : 
	forall n:nat, n = 0 \/ n = S (pred n).

  intros.
  induction n.
    -left. reflexivity.
    -right. simpl. reflexivity.
Qed.



Lemma mult_eq_O : 
	forall (n m:nat), n * m = 0 -> n = 0 \/ m = 0.

  intros.
  induction n.
    -left.  reflexivity.
    -induction m.
      +right. reflexivity.
      +simpl in H. inversion H.
Qed.


Theorem or_commut : 
	forall (P Q:Prop), P \/ Q -> Q \/ P.

  intros.
  destruct H.
    -right. apply H.
    -left. apply H.
Qed.


Check True.


Theorem ex_falso_quodlibet : 
  forall (P:Prop), False -> P.
  
  intros.
  destruct H.
Qed.



Fact not_implies_our_not:
  forall P:Prop, ~P -> (forall Q:Prop, P -> Q).

  intros P H Q NP.
  apply H in NP.
  destruct NP.
Qed.

Theorem zero_not_one : 
  ~(1 = 0).

  intros contr.
  inversion contr.
Qed.

Check 0 <> 1.


Theorem zero_not_one' : 
   1 <> 0.

  intros H.
  inversion H.
Qed.


(* some exercise *)
Theorem not_False : 
  ~False.

  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : 
  forall (P Q:Prop), (P /\ ~P) -> Q.

  intros.
  destruct H.
  apply H0 in H.
  destruct H.
Qed.

Theorem double_neg : 
  forall P:Prop, P -> ~~P.

Proof.
  intros.
  intros NP.
  apply NP in H.
  destruct H.
Qed.

Theorem contrapositive : 
  forall (P Q:Prop), (P -> Q) -> (~Q -> ~P).

Proof.
  intros.
  intros NP.
  apply H in NP.
  apply H0 in NP.
  destruct NP.
Qed.

Theorem not_both_true_and_false : 
  forall P:Prop, ~(P /\ ~P).

Proof.
  intros.
  unfold not.
  intros N.
  destruct N.
  apply H0 in H.
  destruct H.
Qed.



Theorem not_true_is_false : 
  forall b:bool, b <> true -> b = false.

Proof.
  intros.
  destruct b.
    -unfold not in H.
     apply ex_falso_quodlibet.
     apply H.
     reflexivity.
    -reflexivity.
Qed.



Theorem not_true_is_false' : 
  forall b:bool, b <> true -> b = false.

Proof.
  intros.
  destruct b.
    -unfold not in H.
     exfalso.
     apply H. reflexivity.
    -reflexivity.
Qed.





Check not.

Lemma True_is_true: True.

Proof.
  apply I.
Qed.

Check @eq.
 

Theorem iff_sym : 
  forall (P Q:Prop), (P <-> Q) -> (Q <-> P).
Proof.
  intros.
  unfold iff in H.
  destruct H.
  split.
    -apply H0.
    -apply H.
Qed.



Module MyIff.

Definition iff (P Q:Prop):Prop :=
  (P -> Q) /\ (Q -> P).

Notation "P < - > Q" := (iff P Q)
  (at level 95, no associativity)
  : type_scope.

End MyIff.




Lemma not_true_iff_false : 
  forall b:bool, b <> true <-> b = false.
Proof.
  intros.
  unfold iff.
  split.
    -intros H.
     unfold not in H.
     induction b.
      +exfalso. apply H. reflexivity.
      +reflexivity.
    -intros H.
     unfold not.
     intros H1. rewrite H in H1. inversion H1.
Qed.


(*exercises*)
Theorem iff_refl : 
  forall P:Prop, P <-> P.
Proof.
  intros.
  unfold iff. split.
    -intros H. apply H.
    -intros H. apply H.
Qed.



Theorem iff_trans : 
  forall (P Q R:Prop), (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  destruct H.
  destruct H0.
  split.
    -intros N. apply H in N. apply H0 in N. apply N.
    -intros N. apply H2 in N. apply H1 in N. apply N.
Qed.


Theorem or_distributes_over_and : 
  forall (P Q R:Prop), P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
    -intros H.
     split.
      +destruct H.
        *left. apply H.
        *destruct H. right. apply H.
      +destruct H.
        *left. apply H.
        *destruct H. right. apply H0.
    -intros H.
     destruct H.
     destruct H.
      +left. apply H.
      +destruct H0. *left. apply H0. *right. split. {apply H. } {apply H0. }
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_O : 
  forall (n m:nat), n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros.
  split.
    -apply mult_eq_O.
    -apply or_example.
Qed.

Lemma or_assoc : 
  forall (P Q R:Prop), P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros. split.
    -intros H. destruct H.
      +left. left. apply H.
      +destruct H. *left. right. apply H. *right. apply H.
    -intros H. destruct H.
      +destruct H. *left. apply H. *right. left. apply H.
      +right. right. apply H.
Qed.



Lemma mult_O_3 : 
  forall (n m p:nat), n*m*p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  rewrite mult_O. rewrite mult_O.
  rewrite or_assoc.
  reflexivity.
Qed.



Lemma apply_iff_example : 
  forall (n m:nat), n*m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  apply mult_O.
  apply H.
Qed.
















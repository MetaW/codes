(*
	包含:
	1.
	2.
	3.
	4.
*)


Require Export poly.
Require Export lists.
Require Export tactics.


(* logic connectives *)
(*------------------------------------------------------*)
(* conjunction:/\ and destruct/split*)
(*
	注意:split只能用于goal，将goal分为两个subgaol，如果hypo
		中有/\，应该用destruct来将其分为两个新的hypo，这里不要
		加in。
		eg: destruct H as [HA HB]
*)
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


(* disjunction: \/ and destruct/left right*)
(*
	注意:当\/出现在hypo时，仍然用destruct将其分为两个新hypo，但与/\的
		情况不同，\/时用destruct会产生两个一样的subgoal，分别用两个新hypo
		来证明它，即\/的两侧每一个单独出现都能证出goal。

		当\/出现在goal中时，即任何情况下\/两侧有一个成立即可，用left选择证左边的，
		用right选择证右边的。
*)
Lemma or_example : 
	forall (n m:nat), n = 0 \/ m = 0 -> n*m = 0.

  intros.
  destruct H.		(*destruct后产生两个subgoal*)
    -rewrite H. reflexivity.
    -rewrite H. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro : 
	forall (A B:Prop), A -> A \/ B.

  intros.
  left.			(*这里选择证左边的A*)
  apply H.
Qed.

Lemma zero_or_succ : 
	forall n:nat, n = 0 \/ n = S (pred n).

  intros.
  induction n.			(*对n的两种情况分别选择左边的和右边的*)
    -left. reflexivity.	
    -right. simpl. reflexivity.
Qed.

(*exercises*)

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

/// to page 117.










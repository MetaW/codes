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










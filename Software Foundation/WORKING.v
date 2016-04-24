Check 2 <> 3.

Require Export logic.

Inductive ev : nat -> Prop :=
  | ev_O : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(*其中第一行相当于声明一个函数*)
(*第2，3行相当于两个theorem*)
Theorem ev_4 :
	ev 4.
Proof.
  apply ev_SS.
  apply (ev_SS 0 (ev_O)).
Qed.
	

Theorem ev_plus4 : 
	forall n:nat, ev n -> ev (4+n).
Proof.
  intros.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Theorem ev_double : 
	forall n:nat, ev (double n).
Proof.
  intros.
  induction n.
    -simpl.
     apply ev_O.
    -simpl.
     apply ev_SS.
     apply IHn.
Qed.



Theorem evenb_minus2 : 
	forall n:nat, evenb n = true -> evenb (pred (pred n)) = true.
Proof.
  intros [|[|n']].
    -simpl. reflexivity.
    -simpl. intros H. inversion H.
    -simpl. intros H. apply H.
Qed.


Theorem ev_minus2 : 
	forall n:nat, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E.
    -simpl. apply ev_O.
    -simpl. apply H.
Qed.

Theorem evSS_ev : 
	forall n:nat, ev (S (S n)) -> ev n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.



Theorem one_not_even : 
	~(ev 1).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem SSSSev_even : 
	forall n:nat, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsence : 
	ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.


Theorem ev_even : 
	forall n:nat, ev n -> exists k:nat, n = double k.
Proof.
  intros n E.
  induction E.
    -exists 0. reflexivity.
    -destruct IHE. exists (S x). simpl.
     rewrite H. reflexivity.
Qed.







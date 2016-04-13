(*
	包含：
	1.
	2.
*)


(*###################################################*)
Require Export basic.

(*先看一个例子*)
Theorem plus_n_O_try : 
	forall n:nat, n = n + 0.

Proof.
  intros n.
  induction n.
    -reflexivity.
    -simpl.
     rewrite <- IHn.
     reflexivity.
Qed.

(*
  这就是归纳证明，将目标分为两个子目标，先证明base的情况
  再证明induction的情况，证明induction情况时会自动有一个
  已成立的低一阶的同样的目标作为已知(归纳假设)，利用这个已知就好证明了。
*)


(*one more case*)
Theorem minus_same : 
  forall n:nat, myminus n n = 0.

Proof.
  intros n.
  induction n.
    -reflexivity.
    -simpl.
     rewrite -> IHn.
     reflexivity.
Qed.


(*a list of exercises*)

Theorem multy_O_n : 
  forall n:nat, n*0 = 0.
Proof.
  intros n.
  induction n.
    -reflexivity.
    -simpl.
     rewrite IHn.
     reflexivity.
Qed.

Theorem plus_n_Sm : 
  forall n m:nat, S (n + m) = n + (S m).

  intros n m.
  induction n.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHn.
     reflexivity.
Qed.

(*下面这个例子展示了如何利用以证明过的定理!!!*)
Theorem plus_commu : 
  forall n m:nat, n+m = m+n.

  intros n m.
  induction n as [| n'].
    -simpl.
     rewrite <- plus_n_O_try.   (*利用上门证明的n=n+0*)
     reflexivity.
    -simpl.
     rewrite <- plus_n_Sm.      (*利用上门证明的S (n+m)=n+(S m)*)
     rewrite IHn'.
     reflexivity.
Qed.


//// to page 45.




 
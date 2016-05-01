(*
	包含：
	1.induction归纳证明
	2.使用已经证明过的定理
  3.assert的使用
*)


(*#####################################################*)
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



(*---------------------------下面这个例子展示了如何利用以证明过的定理!!!*)
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

(*another proof*)
Theorem plus_assoc :
  forall n m p:nat, n + (m + p) = (n + m) + p.

  intros n m p.
  induction n as [|n'].
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHn'.
     reflexivity.
Qed.

(*one more*)
Fixpoint double (n:nat) :nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_plus :
  forall n:nat, double n = n + n.

  intros n.
  induction n.
  -simpl.
   reflexivity.
  -simpl.
   rewrite IHn.
   rewrite plus_n_Sm.
   reflexivity.
Qed.


Theorem bigeer_than :
  forall n:nat, n + 1 > O.

  intros n.
  induction n.
  -auto.
  -simpl.
   auto.
Qed.


(*assert*)
(*-----------------------------------------------------------*)
(*首先看一个例子*)

Theorem plus_rearrange_fst : 
	forall n m p q:nat, (n+m)+(p+q) = (m+n)+(p+q).

(*
  intros n m p q.		此时subgoal为：n + m + (p + q) = m + n + (p + q)
  rewrite plus_commu.	此时subgoal为：p + q + (n + m) = m + n + (p + q)
  Abort.				Coq不知道如何正确利用plus——commu,plus_commu中有forall所以
  						上面的subgoal有多处可以匹配plus_commu.
*)
(*这时就可以用assert*)
Proof. 
	intros n m p q.
	assert(H:n+m = m+n).
    	{rewrite plus_commu. reflexivity. }
    rewrite H.
    reflexivity.
Qed.
(*
	assert 将原问题中的子问题提取出来,将原目标分为两个目标，其中一个为assert中的
	在{}中单独证明它，证明之后就会变成已知H。之后又回到原目标，可以在原目标中用rewrite
	使用已证的H来完成证明。这样就避免了证明目标过大时直接利用rewrite导致的问题。
*)

(*exercise*)
(*不要使用induction*)
Theorem plus_swap : 
  forall n m p:nat, n + (m + p) = m + (n + p).

  intros n m p.
  assert(H: n+(m+p) = (n+m)+p).
    {rewrite plus_assoc. reflexivity. }
  rewrite H.
  assert(H1: m+(n+p) = (m+n)+p).
    {rewrite plus_assoc. reflexivity. }
  rewrite H1.
  assert(H2: n + m = m + n).
    {rewrite plus_commu. reflexivity. }
  rewrite H2.
  reflexivity.
Qed.


(*exercise*)

(*辅助后面的证明*)
Theorem mult_comm_help : 
  forall n m:nat, m + m*n = m*(S n).
  
  intros n m.
  induction m.
    -simpl.
     reflexivity.
    -simpl.
     rewrite <- IHm.
     rewrite plus_swap.
     reflexivity.
Qed.


Theorem mult_comm : 
  forall n m:nat, n * m = m * n.

  intros n m.
  induction n as [|n'].
    -simpl.
     rewrite multy_O_n.
     reflexivity.
    -simpl.
     rewrite <- mult_comm_help.
     rewrite IHn'.
     reflexivity.
Qed.






















 
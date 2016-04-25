(*
	包含:
	1. 归纳定义返回Prop类型的函数
	2. inversion on hypo
	3. induction on hypo
	4.

*)

Require Export logic.
(*
	返回Prop的函数的定义:
	  如何定义一个函数:根据计算理论，可以给出基于图灵机的函数实体，即一般的函数
	定义，也可以使用lambda演算来定义函数实体，除此之外还有一种方法，即归纳定义
	一个函数(或递归函数)。某些情况下，函数的返回值用一个实体来计算非常麻烦，而对
	返回值进行归纳定义却比较简单，如斐波那契函数，这些函数可以没有实体，但要有一些
	基础项(base),和归纳规则(induction rule)。
	  同理返回Prop的函数也有上面的性质，前面讲的返回Prop的函数都适用Defi或fixp
	定义的实体，这一节讲如何用base和induction rule来定义返回Prop的函数。
*)

(* 假设我们定义一个判断是非为偶数的函数 ev *)
(*归纳定义函数也用Inductive*)

Inductive ev : nat -> Prop :=
  | ev_O : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(*其中第一行相当于定义一个没有实体的函数*)
(*第2，3行相当于两个theorem*)

Theorem ev_4 :
	ev 4.
Proof.
  apply ev_SS.		(*像使用theorem一样*)
  apply ev_SS.
  apply ev_O.
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
  intros [|[|n']].			(*!!!!!!!!!!*)
    -simpl. reflexivity.
    -simpl. intros H. inversion H.
    -simpl. intros H. apply H.
Qed.


(* inversion on "ev X"(evidence) *)

Theorem ev_minus2 : 
	forall n:nat, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E.			(*   *)
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
  inversion H.				(*   *)
Qed.

(*exercises*)
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


(* induction on "ev X" (evidence) *)

Theorem ev_even : 
	forall n:nat, ev n -> exists k:nat, n = double k.
Proof.
  intros n E.
  induction E.
    -exists 0. reflexivity.
    -destruct IHE. exists (S x). simpl.
     rewrite H. reflexivity.
Qed.

// to page 143.




















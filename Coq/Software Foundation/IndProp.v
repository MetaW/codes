(*
	包含:
	1. 用inductive定义单参数返回Prop类型的函数
	2. inversion on hypo
	3. induction on hypo
	4. 用inductive定义多个参数的返回Prop的函数
	5. 应用:正则表达式的定义与匹配判断
	
*)


Require Export logic.
Require Export lists.
Require Export poly.

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

(*用inductive定义单参数返回Prop类型的函数*)
(* 
	假设我们定义一个判断是非为偶数的函数 ev
	归纳定义函数也用Inductive
*)

Inductive ev : nat -> Prop :=
  | ev_O : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).
(*
	其中第一行相当于定义一个没有实体的函数,
	第2，3行相当于两个默认已成立的关于上面
	的函数的事实(theorem)
*)

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







(* inversion on hypo: "ev X" *)
(*-------------------------------------------------------------------*)
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







(* induction on hypo: "ev X" *)
(*-------------------------------------------------------------------*)
(*
	如果hypo是由inductive定义出来的,那么可以对其使用induction来归纳
	证明. 有时对某个数据的归纳时，将规模减1不能完成证明，而必须将规模减少
	一个大于1的量，如这里对"ev n"的证明，这时对某个数据进行induction将无
	法完成证明，而应该对hypo进行induction.
*)
Theorem ev_even : 
	forall n:nat, ev n -> exists k:nat, n = double k.
Proof.
  intros n E.
  induction E.		(*对hypo 进行归纳证明*)
    -exists 0. reflexivity.
    -destruct IHE. exists (S x). simpl.
     rewrite H. reflexivity.
Qed.



Theorem ev_even_iff : 
	forall n:nat, ev n <-> exists k:nat, n = double k.
Proof.
  intros.
  unfold iff.
  split.
    -intros. apply ev_even. apply H.
    -intros. destruct H. rewrite H. apply ev_double.
Qed.

(* exercise *)
Theorem ev_sum : 
	forall (n m:nat), ev n -> ev m -> ev (n + m).
Proof.
  intros. induction H.
    -apply H0.
    -simpl. apply ev_SS.
     apply IHev.
Qed.


(*归纳定义一个返回hypo的函数方法可能不止一种,eg:*)
Inductive ev' : nat -> Prop :=
  | ev'_O : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum : forall (n m:nat), ev' n -> ev' m -> ev' (n + m).

Lemma plus_n_2:
  forall n:nat, n + 2 = S (S n).
Proof.
  intros.
  induction n.
    -reflexivity.
    -rewrite <- IHn.
     simpl. reflexivity.
Qed.


Theorem ev'_ev : 
	forall n:nat, ev' n <-> ev n.
Proof.
  intros. split.
    -intros.
     induction H.
      +apply ev_O. +apply ev_SS. apply ev_O.
      +apply ev_sum. *apply IHev'1. * apply IHev'2.
    -intros. induction H.
      +apply ev'_O.
      +rewrite <- plus_n_2.
       apply ev'_sum.
        *apply IHev. *apply ev'_2.
Qed.


Theorem ev_ev__ev : 
	forall (n m:nat), ev (n + m) -> ev n -> ev m.
Proof.
  intros.
  induction H0.
    -simpl in H. apply H.
    -apply IHev. simpl in H.
     inversion H. apply H2.
Qed.







(*归纳定义多个参数的返回Prop的函数*)
(*-------------------------------------------------------------------*)

Module LeModule.

(*eg:定义一个nat上的判断小于等于函数*)
Inductive le : nat -> nat -> Prop :=
  | le_n : forall n:nat, le n n
  | le_S : forall (n m:nat), le n m -> le n (S m).

Notation "n <= m" := (le n m).

End LeModule.

(*用上门定义再定义一个nat上的判断小于函数*)
Definition lt (n m:nat) := le (S n) m.

Notation "n < m" := (lt n m).

(*更多的例子*)
Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n*n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n:nat, ev (S n) -> next_even n (S n)
  | ne_2 : forall n:nat, ev (S (S n)) -> next_even n (S (S n)).


Inductive total_relation : nat -> nat -> Prop :=
  | always : forall  (n m:nat), True -> (total_relation n m).

Inductive empty_relation : nat -> nat -> Prop :=
  | never : forall  (n m:nat), (empty_relation n m) -> Flase.


(*再定义个3参数的返回Prop的函数*)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall (m n o:nat), R m n o -> R (S m) n (S o)
  | c3 : forall (m n o:nat), R m n o -> R m (S n) (S o)
  | c4 : forall (m n o:nat), R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall (m n o:nat), R m n o -> R n m 0.

Definition fR (n m:nat):nat :=
  n + m.


Lemma plus_prop:
  forall (n m:nat), n + S m = S (n + m).
Proof.
  intros.
  induction n.
    -simpl. auto.
    -simpl. rewrite IHn. auto.
Qed.

Lemma plus_commu:
  forall (n m:nat), n + m = m + n.
Proof.
  intros.
  induction m.
    -simpl. induction n. +auto. +simpl. rewrite IHn. auto.
    -simpl. rewrite <- IHm. rewrite plus_prop. auto.
Qed.

(* exercise *)
Theorem R_eq_fR : 
	forall (n m o:nat), R n m o <-> fR n m = o.
Proof.
  split.
    -unfold fR. intros.
     induction H.
      +reflexivity.
      +rewrite <- IHR. reflexivity.
      +rewrite <- IHR. auto.
      +simpl in IHR. inversion IHR. rewrite plus_prop in H1. inversion H1. auto.
      +rewrite <- IHR. apply plus_commu.
    -unfold fR. generalize dependent o. induction n.
      +induction m. *simpl. intros. rewrite <- H. apply c1.
        *intros. simpl in H. rewrite <- H. apply c3. apply IHm. reflexivity.
      +induction m.
        *simpl. intros. rewrite <- H. rewrite plus_commu. simpl. apply c2. apply IHn. auto.
        *intros. rewrite <- H. simpl. apply c2. apply IHn. reflexivity.
Qed.

(* exercise *)
Inductive subseq : list nat -> list nat -> Prop :=
  | sqc1 : forall (l:list nat), subseq l l
  | sqc2 : forall (l1 l2 l3:list nat), subseq l1 l2 -> subseq l1 (l2 ++ l3)
  | sqc3 : forall (lx llx ly lly:list nat), subseq lx llx -> subseq ly lly -> subseq (lx ++ ly) (llx ++ lly).












(*正则表达式的定义与匹配的判断*)
(*-------------------------------------------------------------------*)

(*归纳定义多态类型的正则表达式*)
Inductive reg_exp (T:Type) : Type :=
  | EmptySet : reg_exp T 
  | EmptyStr : reg_exp T
  | Char : T -> reg_exp T
  | App : reg_exp T -> reg_exp T -> reg_exp T
  | Union : reg_exp T -> reg_exp T -> reg_exp T
  | Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


(*定义match函数：返回Prop*)

Inductive exp_match {T:Type} : list T -> reg_exp T -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar : forall x:T,  exp_match [x] (Char x)
  | MApp : forall (s1 s2:list T) (re1 re2:reg_exp T), 
                exp_match s1 re1 ->
                exp_match s2 re2 ->
                exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL : forall (s1:list T) (re1 re2:reg_exp T), exp_match s1 re1 
                -> exp_match s1 (Union re1 re2)
  | MUnionR : forall (re1 re2:reg_exp T) (s2: list T), exp_match s2 re2 
                -> exp_match s2 (Union re1 re2)
  | MStarO : forall re:reg_exp T, exp_match [] (Star re)
  | MStarApp : forall (s1 s2:list T) (re:reg_exp T), exp_match s1 re
                -> exp_match s2 (Star re)
                -> exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re)
  (at level 80).


Example reg_exp_ex1: 
    [1] =~ Char 1.
Proof.
  apply MChar.
Qed.


Example reg_exp_ex2: 
    [1,2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _).
    -apply MChar.
    -apply MChar.
Qed.


Example reg_exp_ex3: 
    ~([1,2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.


Fixpoint reg_exp_of_list {T} (l:list T):=
  match l with
  | [] => EmptyStr
  | x:xl => App (Char x) (reg_exp_of_list xl)
  end.


Example reg_exp_ex4: 
    [1,2,3] =~ reg_exp_of_list [1,2,3].
Proof.
  simpl.
  apply (MApp [1] _).
    -apply MChar.
    -apply (MApp [2] _).
      +apply MChar.
      +apply (MApp [3] _).
        *apply MChar.
        *apply MEmpty.
Qed.



















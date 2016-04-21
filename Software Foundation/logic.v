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


(* disjunction: \/ and destruct/left/right*)
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


(* negation: ~/not/True/False/exfalso *)
(*
    在Coq中内置了两个命题False与True,其中False表示矛盾命题,即一个错误的命题,
  True表示一个成立的命题。其中若False出现在了hypo中，可以用destruct H. 来直接
  pass掉当前的goal，或者用inversion H也行。若True出现在了goal中，可以用reflexivity.
  来证明其成立，也可以用apply I来证明(I是Coq提供的专用来证明True成立的定理)

    在Coq中~P表示命题P的否定, 它是 "not P" 的语法糖,而not P的定义为：P -> False.
    因此若在goal中遇到~P,应用unfold not将其展开为 P -> False的形式，或直接用
  intros H,它会自动展开~P并将P引入至hypo中，留下False作为goal. 若~P出现在Hypo中
  就用unfold not将其展开，再进一步处理。

    在证明中会经常遇到goal明显是错误的情况，Coq提供了一个新tactic: exfalso, 它根据
  False -> P, 将goal直接转为False,若命题没有问题那么hypo就一定能够推出矛盾，即得到
  False,因此命题被证明。这样我们可以忽略goal的具体形式，只用False代替它从而化简证明过程。
*)

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


Theorem zero_not_one' : 
   1 <> 0.       (* A <> B 是 ~(A = B)的语法糖*)

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
     apply ex_falso_quodlibet.  (*这个会经常遇到,Coq为它提供了tactic,例如面一个例子*)
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
     exfalso.             (*!!!这等价于上面例子中的apply...，将矛盾的goal转为False*)
     apply H. reflexivity.
    -reflexivity.
Qed.

Lemma True_is_true: True.

Proof. 
  apply I.
Qed.


(*logic equivalence: <-> / iff *)

(* <->的定义 *)
Module MyIff.

Definition iff (P Q:Prop):Prop :=
  (P -> Q) /\ (Q -> P).

Notation "P < - > Q" := (iff P Q)
  (at level 95, no associativity)
  : type_scope.

End MyIff.


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


(*
  //TODO
*)
Require Import Coq.Setoids.Setoid.

(*先证俩定理*)
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


(*使用reerite/reflexivity*)

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






(*Existential Quantification*)
(*---------------------------------------------------------------*)
(*
    //TODO
*)
















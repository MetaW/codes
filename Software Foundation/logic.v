(*
	包含:
	1. /\ and/destruct/split
	2. \/ or/destruct/left/right
	3. ~  not/True/False/exfalso
	4. <-> iff/destruct/split/(rewrite/reflexivity)
  5. exists /destruct
  6. Programming with Type: Prop
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
(*
  逻辑等价用"P <-> Q"来表示，它是函数 iff P Q 的语法糖，函数iff
  的定义为 (P -> Q) /\ (Q -> P)。当<->出现在hypo中时，可以
  unfold iff in H. destruct H. 将其分解为两个hypo，或直接用
  destruct H. 也能达到相同的效果。当<->出现在goal中时，可以先用
  unfold将其展开，再用split将其分为两个subgoal，或者直接用split也行。

*)
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
    与其它逻辑符号不同，由于<->是逻辑等价关系，因此它满足一些特殊的性质，
    1.它能像"="表达式一样支持rewrite和reflexivity。
    2.它能使用apply，并且apply能自动识别出使用<->的那一边(A->B,B->A)来被
      apply使用。
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



(*使用rewrite/reflexivity*)
Lemma mult_O_3 : 
  forall (n m p:nat), n*m*p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  rewrite mult_O. rewrite mult_O.   (*像使用"="一样对<->使用rewrite*)
  rewrite or_assoc.                 
  reflexivity.                      (*能用reflexivity证明"A<->A"形式的定理*)
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
    存在量词出现在hypo中时，还是用destruct，此时会将exists消掉，并引入一个
    新的hypo，它是假设使原hypo成立的那个个体。
    当它出现在goal中时，我们需要为它确定一个使goal成立的个体或表达式，然后使用
    tactic："exists x" 或 "exists (expression)", 之后goal中的exist部分会消掉
    对于的约束变量会用我们给的那个个体或表达式来代替。
*)
Lemma four_is_even : 
  exists n:nat, 4 = n + n.
Proof.
  exists 2.   (*指明n为2*)
  reflexivity.
Qed.

Theorem exists_example2 : 
  forall n:nat, (exists m:nat, n = 4 + m) -> (exists o:nat, n = 4 + o).
Proof.
  intros.
  destruct H. (*将hypo中的exists部分消去*)
  exists x.   (*指明o为x*)
  apply H.
Qed.


Theorem dist_not_exists : 
  forall (X:Type) (P:X->Prop), (forall x:X, P x) -> ~(exists x:X, ~(P x)).
Proof.
  intros.
  unfold not.
  intros H1.
  destruct H1.
  apply H0.
  apply H.
Qed.


Theorem dist_exists_or : 
  forall (X:Type) (P Q: X -> Prop), (exists x:X, P x \/ Q x)<->(exists x:X, P x)\/(exists x:X, Q x).
Proof.
  intros.
  split.
    -intros H.
     destruct H.
     destruct H. 
      +left. exists x. apply H.
      +right. exists x. apply H.
    -intros H.
     destruct H.
      +destruct H. exists x. left. apply H.
      +destruct H. exists x. right. apply H.
Qed.




(*Programming with Type: Prop*)
(*-------------------------------------------------------------------*)
(*
  与其它类型类似，我们将Prop作为函数参数类型类型，返回类型等。
*)

(*返回判断元素x是否在list l中的命题*)
Fixpoint In {X:Type} (x:X) (l:list X) :=
  match l with
  | [] => False
  | h:t => (x=h) \/ In x t
  end.


Example In_example_1: 
  In 4 [3,4,5].
Proof.
  simpl.
  right. left. reflexivity.
Qed.

Example In_example_2:
  forall n:nat, In n [2,4] -> exists n':nat, n = 2*n'.
Proof.
  intros.
  unfold In in H.
  destruct H.
    -exists 1. rewrite H. reflexivity.
    -destruct H. 
      +exists 2. rewrite H. reflexivity.
      +inversion H.
Qed.

Lemma In_map : 
  forall (A B:Type) (f:A -> B) (l:list A) (x:A), In x l -> In (f x) (map f l).
Proof.
  intros.
  induction l.
    -simpl in H. destruct H.
    -simpl.
     simpl in H. destruct H.
      +left. rewrite H. reflexivity.
      +right. apply IHl in H. apply H.
Qed.


(*exercises*)
Example In_map_iff: 
  forall (A B:Type) (f:A->B) (l:list A) (y:B), In y (map f l) <-> exists x:A, f x = y /\ In x l.
Proof.
  intros.
  split.
    -intros. 
     induction l.
      +simpl in H. destruct H.
      +simpl in H. destruct H.
        *exists x. split. {symmetry. apply H. } {simpl. left. reflexivity. }
        *apply IHl in H. destruct H. exists x0. simpl.
         split. {apply H. } {right. apply H. }
    -intros.
     induction l.
      +simpl in H. destruct H. destruct H. destruct H0.
      +simpl. simpl in H. destruct H.
         destruct H. destruct H0.
          *left. rewrite H0 in H. symmetry. apply H.
          *right. apply IHl. exists x0. split. {apply H. } {apply H0. }
Qed.


Lemma In_app_iff : 
  forall (A:Type) (l l':list A) (a:A), In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros.
  split.
    -intros.
     induction l.
      +simpl in H. right. apply H.
      +simpl in H. simpl. apply or_assoc.
       destruct H.
        *left. apply H.
        *right. apply IHl. apply H.
    -intros.
     induction l.
      +simpl. destruct H. {simpl in H. destruct H. } {apply H. }
      +simpl. simpl in H. apply or_assoc in H. destruct H.
        *left. apply H.
        *right. apply IHl. apply H.
Qed.



Fixpoint All {T:Type} (P:T -> Prop) (l:list T):Prop :=
  match l with
  | [] => True
  | h:t => (P h) /\ All P t
  end.

Lemma All_In : 
  forall (T:Type) (P:T -> Prop) (l:list T), (forall x:T, In x l -> P x) <-> All P l.
Proof.
  intros.
  split.
    -intros.
     induction l.
      +simpl. reflexivity.
      +simpl. simpl in H. split.
        *apply H. left. reflexivity.
        *apply IHl. intros. apply H. right. apply H0.
    -intros.
     induction l.
      +simpl in H0. destruct H0.
      +simpl in H. simpl in H0. destruct H0.
        *rewrite <- H0 in H. apply H.
        *apply IHl. { apply H. } {apply H0. }
Qed.



Definition combine_odd_even (Podd Peven :nat -> Prop): nat -> Prop :=
  (fun n => if evenb n then Peven n else Podd n).


Theorem combine_odd_even_intro : 
  forall (Podd Peven :nat -> Prop) (n:nat), 
    (evenb n = false -> Podd n) -> 
    (evenb n = true -> Peven n) ->
    (combine_odd_even Podd Peven n).
Proof.
  intros.
  unfold combine_odd_even.
  destruct (evenb n).
    -apply H0. reflexivity.
    -apply H. reflexivity.
Qed.

(**)
(*-------------------------------------------------------------*)
(*
  
*)

(**)
Axiom functional_extensionality :
  forall (X Y:Type) (f g: X -> Y), (forall x:X, f x = g x) -> f = g.


Fixpoint rev_append {X:Type} (l1 l2:list X):list X :=
  match l1 with
  | [] => l2
  | h:t => rev_append t (h:l2)
  end.

Definition tr_rev {X:Type} (l:list X):list X :=
  rev_append l [].


Lemma rev_append_lemma:
  forall (X:Type) (l1 l2:list X), rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l.
  induction l as [|x0 l'].
    -simpl. reflexivity.
    -simpl. rewrite IHl'. intros l2. 
     assert(H: rev_append l' (x0 : l2) = rev_append l' [ ] ++ (x0:l2)).
      {rewrite IHl'. reflexivity. }
     rewrite H. rewrite <- app_assoc. simpl.
     reflexivity.
Qed.


(*证明函数相等*)
Lemma tr_rev_correct : 
  forall X:Type, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.      (**)
  intros.
  induction x.
    -simpl. unfold tr_rev. simpl. reflexivity.
    -simpl. unfold tr_rev. simpl. rewrite <- IHx.
     unfold tr_rev. rewrite rev_append_lemma.
     reflexivity.
Qed.



Theorem evenb_double : 
  forall k:nat, evenb (double k) = true.
Proof.
  intros.
  induction k.
    -simpl. reflexivity.
    -simpl. apply IHk.
Qed.

Definition notb (b:bool):bool :=
match b with
| true => false
| false => true
end.

Fixpoint oddb (n:nat):bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => oddb n'
  end.

Theorem evenb_double_conv : 
  forall n:nat, (exists (k:nat), n = if evenb n then double k else S (double k)).
Admitted.

Theorem even_bool_prop : 
  forall n:nat, evenb n = true <-> exists k:nat, n = double k.
Proof.
  intros. unfold iff. split.
    -intros. destruct (evenb_double_conv n).
     exists x. rewrite H in H0. apply H0.
    -intros. destruct H. rewrite H. apply evenb_double.
Qed.



(*exercises*)

Lemma andb_true_iff : 
  forall (b1 b2:bool), andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros.
  split.
    -intros. split.
      +destruct b1. *reflexivity. *simpl in H. inversion H.
      +destruct b2. *reflexivity. *destruct b1. {inversion H. } {inversion H. }
    -intros. destruct H. rewrite H. rewrite H0.
     reflexivity.
Qed.

Lemma orb_true_iff : 
  forall (b1 b2:bool), orb b1 b2 = true <-> b1 =true \/ b2 = true.
Proof.
  intros.
  split.
    -intros. destruct b1.
      +left. reflexivity.
      +simpl in H. right. apply H.
    -intros. destruct H. +rewrite H. reflexivity. +rewrite H. destruct b1.
      *reflexivity. *reflexivity.
Qed.

Require Export tactics.

Lemma beq_nat_n_n:
  forall n:nat, beq_nat n n = true.
Proof.
  intros.
  induction n.
    -reflexivity.
    -simpl. apply IHn.
Qed.

Theorem beq_nat_false_iff : 
  forall (x y:nat), beq_nat x y = false <-> x<>y.
Proof.
  intros.
  split.
    -intros. unfold not. intros.
     rewrite H0 in H. 
     induction y.
      +simpl in H. inversion H.
      +simpl in H. rewrite beq_nat_n_n in H. inversion H.
    -generalize dependent y. induction x.
      +intros. induction y. *exfalso. apply H. reflexivity. *reflexivity.
      +induction y.
        *intros. reflexivity.
        *simpl. intros. apply IHx. intros. unfold not. intros. rewrite H0 in H. unfold not in H.
         apply H. reflexivity.
Qed.


// to page 132.








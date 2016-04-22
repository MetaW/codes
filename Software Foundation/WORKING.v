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




Lemma four_is_even : 
  exists n:nat, 4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.



Theorem exists_example2 : 
  forall n:nat, (exists m:nat, n = 4 + m) -> (exists o:nat, n = 4 + o).
Proof.
  intros.
  destruct H.
  exists x.
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



Check combine_odd_even.


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



Check combine_odd_even_intro.


Check @rev.

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

Lemma tr_rev_correct : 
  forall X:Type, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  induction x.
    -simpl. unfold tr_rev. simpl. reflexivity.
    -simpl. unfold tr_rev. simpl. rewrite <- IHx.
     unfold tr_rev. rewrite rev_append_lemma.
     reflexivity.
Qed.
Check evenb.
Check double.



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


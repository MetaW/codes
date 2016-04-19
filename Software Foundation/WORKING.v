(*
	CONTENT	:
	1.
	2.
	3.
	4.
*)

Require Export poly.
Require Export lists.




(* tactic: apply *)
(*-------------------------------------------------------------------------*)
(*look a example*)


Theorem silly1 : 
	forall (n o m p:nat), n = m -> [n,o] = [n,p] -> [n,o] = [m,p].
  intros n o m p eq1 eq2.
  rewrite <- eq1.
  apply eq2.	(*here we use "apply eq2" to replace "rewrite eq2. reflexivity."*)
Qed.


(*another example*)
Theorem silly2 : 
	forall (n o m p:nat), n = m -> (forall (q r:nat), q =r -> [q,o] = [r,p] ) -> [n,o] = [m,p].

  intros n m o p eq1 eq2.
  apply eq2.	(*with hypotheses A->B and goal B, apply A->B to goal B can transfer goal to A*)
  apply eq1.	(*with hypotheses A and goal A apply A can finish the proof*)
Qed.

Theorem silly2a : 
	forall (n m:nat), (n,n) = (m,m) -> (forall (q r:nat), (q,q) = (r,r) -> [q] = [r] ) -> [n] = [m].

  intros.
  apply H0.
  apply H.
Qed.

Fixpoint oddb (n:nat):bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => oddb n'
  end.

Theorem silly_ex : 
	(forall n, evenb n = true -> oddb (S n) = true ) -> evenb 3 = true -> oddb 4 = true.

  intros.
  apply H.
  apply H0.
Qed.

(*
	To use the apply tactic, the knowen fact being applied must 
	match the goal exactly. for example, apply will not work if 
	the left and right sides of the equality are swapped.
	ps: apply a fact with "forall" Coq can auto match the goal if
		it can really match.
*)

Fixpoint beq_nat (n m:nat):bool :=
  match n,m with
  | O,O => true
  | O,_ => false
  | _,O => false
  |S n',S m' => beq_nat n' m'
  end.

Theorem silly3 : 
	forall n:nat, true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.

  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.



Theorem rev_exer : 
	forall (n m:list nat), n = rev m -> m = rev n.

  intros.
  rewrite H.
  symmetry.
  apply  rev_involutive.
Qed.


Lemma trans_eq : 
	forall (X:Type) (n m o:X), n = m -> m = o -> n = o.

	intros X n m o eq1 eq2.
	rewrite <- eq2.
	apply eq1.
Qed.

Example trans_eq_example: 
	forall (a b c d e f:nat), [a,b] = [c,d] -> [c,d] = [e,f] -> [a,b] = [e,f].

  intros.
  apply trans_eq with [c,d].
  apply H.
  apply H0.
Qed.

Theorem S_injective : 
	forall (n m:nat), S n = S m -> n = m.

  intros.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : 
	forall (n m o:nat), [n,m] = [o,o] -> [n] = [m].
  
  intros.
  inversion H.
  reflexivity.
Qed.


Theorem inversion_ex2 : 
	forall (n m:nat), [n] = [m] -> n = m.

  intros.
  inversion H as [W].
  reflexivity.
Qed.


Theorem inversion_ex3 : 
	forall (X:Type) (x y z:X) (l j:list X), x:y:l = z:j -> y:l = x:j -> x = y.

  intros.
  inversion H0.
  reflexivity.
Qed.

Theorem inversion_ex4 : 
	true = false -> 1 + 1 = 3.
  
  intros.
  inversion H.
Qed.



Theorem inversion_ex5 : 
	forall n:nat, S n = O -> 1 + 1 = 12345.

  intros.
  inversion H.
Qed.

Example inversion_ex6: 
	forall (X:Type) (x y z:X) (l j:list X), x:y:l = [] -> y:l = z:j -> x=z.

  intros.
  inversion H.
Qed.


Theorem S_inj : 
  forall (n m:nat) (b :bool), beq_nat (S n) (S m) = b -> beq_nat n m = b.

  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly_ex1 : 
  forall n:nat, (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) -> true = beq_nat n 5 -> true = beq_nat (S (S n)) 7.

  intros.
  symmetry in H0.
  apply H in H0.
  symmetry.
  apply H0.
Qed.



Theorem plus_n_n_injective : 
  forall (n m:nat), n+n = m+m -> n = m.

  intros n.
  induction n as [| n'].
   -intros m eq.
    induction m as [| m'].
     +reflexivity.
     +inversion eq.
   -intros m eq.
    induction m as [| m].
     +inversion eq.
     +apply f_equal.
      rewrite <- plus_n_Sm in eq.
      simpl in eq.
      rewrite <- plus_n_Sm in eq.
      inversion eq.
      apply IHn' in H0.
      apply H0.
Qed.

Theorem double_injective : 
  forall (n m:nat), double n = double m -> n = m.

  intros n.
  induction n as [| n'].
    -simpl. intros m eq. 
     induction m as [|m'].
      +reflexivity.
      +inversion eq.
    -simpl.
     intros m eq.
     induction m as [|m'].
      +simpl in eq.  inversion eq.
      +apply f_equal.
       apply IHn'.
       simpl in eq.
       inversion eq.
       reflexivity.
Qed.


Theorem beq_nat_true:
  forall (n m:nat), beq_nat n m = true -> n = m.
  
  intros n.
  induction n as [|n'].
    -simpl. intros m eq.
     induction m as [|m'].
      +reflexivity.
      +inversion eq.
    -simpl. intros m eq.
     induction m as [|m'].
      +inversion eq.
      +apply IHn' in eq.
       apply f_equal.
       apply eq.
Qed.


Theorem double_injective2 : 
  forall (n m:nat), double n = double m -> n = m.

  intros n m.
  generalize dependent n.
  induction m as [|m'].
    -simpl. intros n eq.
     induction n as [|n'].
      +reflexivity.
      +simpl in eq. inversion eq.
    -simpl. intros n eq.
     induction n as [|n'].
      +inversion eq.
      +simpl in eq.
       inversion eq.
       apply IHm' in H0.
       apply f_equal.
       apply H0.
Qed.

(*aaa*)

Theorem nth_error_after_last:
  forall (n:nat) (X:Type) (l:list X), length l = n -> nth_error l n = none.

  intros n X.
  induction n.
    -intros l eq.
     induction l.
      +simpl. reflexivity.
      +simpl. inversion eq.
    -intros l eq.
     induction l.
      +simpl. reflexivity.
      +simpl. simpl in eq.
       inversion eq.
       rewrite H0.
       apply IHn in H0.
       apply H0.
Qed.


Theorem app_length_cons : 
  forall (X:Type) (l1 l2:list X) (x:X) (n:nat), length (l1 ++ (x:l2)) = n -> S (length (l1 ++ l2)) = n.

  intros X l1.
  induction l1.
    -intros l2 x n.
      +simpl. intros eq. apply eq.
    -intros l2 x0 n eq.
     simpl. simpl in eq.
     induction n.
      +inversion eq.
      +inversion eq.
       rewrite H0.
       apply IHl1 in H0.
       apply f_equal.
       apply H0.
Qed.

Theorem app_length_twice : 
  forall (X:Type) (n:nat) (l:list X), length l = n -> length (l ++ l) = n + n.

  intros X n.
  induction n.
    -intros l eq.
     induction l.
      +simpl. reflexivity.
      +simpl in eq. inversion eq.
    -intros l eq.
     induction l.
      +simpl in eq. inversion eq.
      +simpl in eq. inversion eq.
       simpl. apply f_equal.
       rewrite H0.
       rewrite app_length.
       simpl. rewrite H0.
       reflexivity.
Qed.

Theorem double_induction : 
  forall (P:nat -> nat -> Prop), P O O -> (forall (m:nat), P m O -> P (S m) O)
    -> (forall n:nat, P O n -> P O (S n)) -> (forall (m n:nat), P m n -> P (S m) (S n)) -> forall (m n:nat), P m n.

  intros P.
  intros P0.
  intros H1.
  intros H2.
  intros H3.
  intros m.
  induction m.
    -intros n.
     induction n.
      +apply P0.
      +apply H2 in IHn.
       apply IHn.
    -intros n.
     induction n.
      +apply H1 in IHm. apply IHm.
      +apply H3.
       apply IHm.
Qed.

    







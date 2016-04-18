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

Theorem silly3a : 
	forall n:nat, true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.

  intros.
  simpl.
  symmetry.
  apply H.s
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






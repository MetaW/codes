(*
  contents:
  1. 自动产生的induction principle,手写induction principle.
  2. 
  3.
  4.
  5.
*)

Require Export I_proofObjects.




(* 自动产生的induction principle *)
(*--------------------------------------------------------*)
(*
Every time we declare a new Inductive datatype, Coq
automatically generates an induction principle for this type.
This induction principle is a theorem like any other: If t is 
defined inductively, the corresponding induction principle is 
called t_ind.

eg: nat_ind
*)
Check nat_ind.
(*
nat_ind
     : forall P : nat -> Prop,
       P 0 ->
       (forall n : nat, P n -> P (S n)) ->
       forall n : nat, P n
*)


(*
  induction tactic其实就是apply t_ind!!!
*)
(*example*)
Theorem mult_0_r' : forall n, n * 0 = 0.
Proof.
  apply nat_ind.  (* 不用induction,手动调用nat_ind *)
  -auto.
  -simpl. intros. apply H.
  Show Proof.
Qed.

(* exercise *)
Theorem plus_one_r' : forall n, n + 1 = S n.
Proof.
  apply nat_ind.
  -auto.
  -simpl. intros. rewrite H. apply eq_refl.
  Show Proof.
Qed.


(* 手写induction principle *)
Inductive yesno : Type :=
| yes : yesno
| no  : yesno.
Definition yesno_ind' : forall P : yesno -> Prop, 
                        P yes ->
                        P no  ->
                        (forall y : yesno, P y).


Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.
Definition natlist_ind' : forall P : natlist -> Prop,
                          P nnil ->
                          (forall n nl, P nl -> P (ncons n nl)) ->
                          (forall y : natlist, P y).


Inductive natlist1 : Type :=
| nnil1 : natlist1
| ncons1 : natlist1 -> nat -> natlist1.
Definition natlist1_ind' : forall P : natlist1 -> Prop,
                           P nnil1 ->
                           (forall nl n, P nl -> P (ncons1 nl n)) ->
                           (forall y : natlist1, P y).


Inductive byntree : Type :=
| bempty : byntree
| bleaf : yesno -> byntree
| nbranch : yesno -> byntree -> byntree -> byntree.
Definition byntree_ind' : forall P : byntree -> Prop,
                          P bempty ->
                          (forall y:yesno, P (bleaf y)) ->
                          (forall (y : yesno) (t1 t2 : byntree), 
                            P t1 -> P t2 -> P (nbranch y t1 t2)) -> 
                          (forall t:byntree, P t).



(* polymorphisom 的情况 *)
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

(* just add a (X:Type) in params, let list_ind' be a 
polymorphisom function *)
Definition list_ind' : forall (X : Type) (P : list X -> Prop),
                       P (nil X)-> 
                       (forall (x : X) (li : list X), 
                          P li -> P (cons X x li)) ->
                       (forall li : list X, P li).











(*--------------------------------------------------------*)
(*--------------------------------------------------------*)
(*--------------------------------------------------------*)
(*--------------------------------------------------------*)
(*--------------------------------------------------------*)
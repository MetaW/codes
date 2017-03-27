(*
  contents:
  1.
  2.
  3.
  4.
  5.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import H_maps.
Require Import L_imp.


(*
之前使用的imp程序比较简单，又因为state有默认值，因此程序
除非是死循环，否则一定正常中止。不会进入为定义状态。但当语言变的
稍微复杂时，有些程序可能无法正常中止,(eg:1+nil). 此时我们可以
给语言加类型并进行类型检查。

使用small step的好处：
1. 方便讨论concurency的语言
2. 能够区分distinguish nontermination from "stuck states."
*)


(* A toy language *)
(*-----------------------------------------------------*)
Inductive tm : Type :=
| C : nat -> tm       (* Constant *)
| P : tm -> tm -> tm. (* Plus *)

(* big step style *)
(* function *)
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

(* relation *)
Reserved Notation " t '||' n " (at level 50, left associativity).
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n || n
  | E_Plus : forall t1 t2 n1 n2,
      t1 || n1 ->
      t2 || n2 ->
      P t1 t2 || (n1 + n2)
  where " t '||' n " := (eval t n).


Module SimpleArith1.
(* small step *)
Reserved Notation " t '==>' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ==> t2' ->
      P (C n1) t2 ==> P (C n1) t2'
  where " t '==>' t' " := (step t t').


Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      ==>
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1.
  apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      ==>
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  apply ST_Plus2.
  apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.

End SimpleArith1.









(*-----------------------------------------------------*)
Definition relation (X: Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros.
  -inversion H0. +reflexivity. +subst. inversion H3.
   +subst. inversion H3.
  -inversion H0.
   +subst. inversion H.
   +subst. assert (t1' = t1'0).
    *apply IHstep in H4. assumption.
    *subst. reflexivity.
   +subst. inversion H.
  -inversion H0.
   +subst. inversion H.
   +subst. inversion H4.
   +subst. assert (t2'=t2'0).
    *apply IHstep in H4. assumption.
    *subst. reflexivity.
Qed.

End SimpleArith2.









(*-----------------------------------------------------*)
(*-----------------------------------------------------*)
(*-----------------------------------------------------*)
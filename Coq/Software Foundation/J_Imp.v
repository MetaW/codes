Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.


Module AExp.


(* abstract syntex tree *)
(*------------------------------------------------------*)
(* auxiliary *)



(* AST *)
Inductive aexp:Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp:Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Inductive com:Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.









(* optimization *)
(*------------------------------------------------------*)

(* 0 + n --> n *)
Fixpoint optimize_0plus (exp:aexp) :aexp :=
  match exp with
  | ANum n            => ANum n
  | APlus (ANum 0) e2 => (optimize_0plus e2)
  | APlus e1 e2       => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2      => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2       => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(* true and x --> x *)
Fixpoint optimize_true_and (exp:bexp):bexp :=
  match exp with
  | BTrue         => BTrue
  | BFalse        => BFalse
  | BEq ae1 ae2   => BEq (optimize_0plus ae1) (optimize_0plus ae2)
  | BLe ae1 ae2   => BLe (optimize_0plus ae1) (optimize_0plus ae2)
  | BNot be1      => BNot (optimize_true_and be1)
  | BAnd BTrue be2 => optimize_true_and be2
  | BAnd be1 be2  => BAnd (optimize_true_and be1) (optimize_true_and be2)
  end.








(* eval *)
(*------------------------------------------------------*)

Fixpoint aeval (exp:aexp): nat :=
  match exp with
  | ANum n            => n
  | APlus exp1 exp2   => (aeval exp1) + (aeval exp2)
  | AMinus exp1 exp2  => (aeval exp1) - (aeval exp2)
  | AMult exp1 exp2   => (aeval exp1) * (aeval exp2)
  end.

  Example Test_aeval : aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof.
    simpl.
    reflexivity.
  Qed.

Fixpoint beval (exp:bexp): bool :=
  match exp with
  | BTrue           => true
  | BFalse          => false
  | BEq exp1 exp2   => beq_nat (aeval exp1) (aeval exp2)
  | BLe exp1 exp2   => leb (aeval exp1) (aeval exp2)
  | BNot exp1       => negb (beval exp1)
  | BAnd exp1 exp2  => andb (beval exp1) (beval exp2)
  end.











(* prove *)
(*
  1. tactic: try, ;, repeat
  2. 
  
*)
(*------------------------------------------------------*)
(*------------------------------------------------------*)
(* prove optimize_0plus is soundness *)
Theorem optimize_0plus_sound: 
  forall exp, aeval (optimize_0plus exp) = aeval exp.
Proof.
  intros.
  induction exp;
  try (simpl;rewrite IHexp1; rewrite IHexp2; reflexivity).
  -simpl. reflexivity.
  -destruct exp1;
   try(simpl; simpl in IHexp1; rewrite IHexp1; rewrite IHexp2; reflexivity).
   +destruct n;simpl; rewrite IHexp2; reflexivity.
Qed.



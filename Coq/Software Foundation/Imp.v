Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.


Module AExp.


(* abstract syntex tree *)
(*------------------------------------------------------*)
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








(* optimization *)
(*------------------------------------------------------*)

(* 0 + n --> n *)
Fixpoint optimize_0plus (exp:aexp) :aexp:=
  match exp with
  | ANum n            => ANum n
  | APlus (ANum 0) e2 => (optimize_0plus e2)
  | APlus e1 e2       => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2      => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2       => AMult (optimize_0plus e1) (optimize_0plus e2)
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




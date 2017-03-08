(*
  contents:
  1. behaviorally equivalent
  2. Properties of Behavioral Equivalence
      -equivance relation
      -Congruence
  3. Program Transformations
  4. Proving That Programs Are Not Equivalent
  5. Nondeterministic Imp

*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import H_maps.
Require Import L_imp.


(*behaviorally equivalent*)
(*---------------------------------------------------*)
(*
对于aexp,bexp这类程序, behaviorally equivalent指的是在
任意状态下求值后结果相同。
*)
Definition aequiv (a1 a2:aexp) : Prop := forall st, aeval st a1 = aeval st a2.

Definition bequiv (b1 b2:bexp) : Prop := forall st,
beval st b1 = beval st b2.


(* example *)
Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  unfold aequiv. intros. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  unfold bequiv. intros. unfold beval. rewrite aequiv_example. auto.
Qed.



(*
对于命令我们不能说两段程序行为等价当且仅当它们从任意相同的状态出发，最终得到的
状态相同，因为某些程序根本不停机，也就不会有最终状态。所以命令程序的等价应
该是：(1):两者都不停机,或(2):都停机且最终的状态相同。
也可以表述为：如果第一个程序停在某个状态上，那么第二个也停在该状态上，反之亦然。
*)
Definition cequiv (c1 c2: com) : Prop := forall st st1,
    c1 / st \\ st1 <-> c2 / st \\ st1.


(*examples*)
Theorem skip_left : forall c, cequiv (SKIP;;c) c.
Proof.
  intros.
  unfold cequiv.
  split.
  -intros.
   inversion H. subst. inversion H2. subst. assumption.
  -intros. apply E_Seq with st.
   +apply E_Skip.
   +assumption.
Qed.


Theorem skip_right : forall c, cequiv (c;;SKIP) c.
Proof.
  intros.
  unfold cequiv.
  split.
  -intros. inversion H. subst. inversion H5. subst. assumption.
  -intros. apply E_Seq with st1.
    +assumption.
    +apply E_Skip.
Qed.


Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros.
  unfold cequiv.
  intros.
  split.
  -intros. inversion H. subst. 
    +assumption. 
    +subst. simpl in H5. inversion H5.
  -intros. apply E_IfTrue.
    +simpl. auto.
    +assumption.
Qed.

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros.
  unfold cequiv.
  intros.
  split.
  -intros. unfold bequiv in H. simpl in H. inversion H0. subst.
   +rewrite H in H6. inversion H6.
   +subst. assumption.
  -intros. unfold bequiv in H. simpl in H. apply E_IfFalse.
   +rewrite H. auto.
   +assumption.
Qed.


Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros.
  unfold cequiv.
  split.
  -intros. inversion H. subst.
    +apply E_IfFalse. *simpl. rewrite H5. auto. *assumption.
    +subst. apply E_IfTrue. *simpl. rewrite H5. auto. *assumption.
  -intros. inversion H; subst.
    +apply E_IfFalse. 
      *simpl in H5. destruct (beval st b). **inversion H5. **auto.
      *assumption.
    +apply E_IfTrue.
      *simpl in H5. destruct (beval st b). **auto. **inversion H5.
      *assumption.
Qed.


Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros.
  unfold bequiv in H. simpl in H. unfold cequiv. split.
  -intros. inversion H0. subst.
    +apply E_Skip. +subst. rewrite H in H3. inversion H3.
  -intros. inversion H0. subst. apply E_WhileEnd. apply H.
Qed.

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  not ( (WHILE b DO c END) / st \\ st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  induction H; inversion Heqcw; subst; clear Heqcw.
  -unfold bequiv in Hb. rewrite Hb in H. simpl in H. inversion H.
  -apply IHceval2. auto.
Qed.

Theorem WHILE_true: forall b c,
  bequiv b BTrue ->
  cequiv
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END).
Proof.
  intros.
  unfold cequiv. split. unfold bequiv in H. simpl in H.
  -intros. apply WHILE_true_nonterm with (c:=c) (st:=st) (st':=st1) in H.
   unfold not in H. apply H in H0. inversion H0.
  -intros. apply WHILE_true_nonterm in H0.
   +inversion H0. +unfold bequiv. simpl. reflexivity.
Qed.


Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros.
  unfold cequiv.
  split.
  -intros. destruct (beval st b) eqn:Hbe.
    +apply E_IfTrue.
     ++inversion H. subst.
      *rewrite H4 in Hbe. inversion Hbe.
      *subst. assumption.
     ++inversion H. subst.
      *rewrite H4 in Hbe. inversion Hbe.
      *subst. apply E_Seq with st2. **assumption. **assumption.
    +apply E_IfFalse.
     ++assumption.
     ++inversion H.
      *subst. apply E_Skip.
      *subst. rewrite H2 in Hbe. inversion Hbe.
  -intros. destruct (beval st b) eqn:Hbe.
    +inversion H. subst.
      *inversion H6. subst. apply E_WhileLoop with st2.
       **assumption. **assumption. **assumption.
      *subst. rewrite H5 in Hbe. inversion Hbe.
    +inversion H. subst.
      *inversion H6. subst. apply E_WhileLoop with st2.
       **assumption. **assumption. **assumption.
      *subst. inversion H6. subst. apply E_WhileEnd. assumption.
Qed.


Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
  intros.
  unfold cequiv.
  split.
  -intros. inversion H. subst.
   assert(st = t_update st X (aeval st (AId X))).
   +apply functional_extensionality.
    intros. simpl. rewrite t_update_same. auto.
   +rewrite <- H0. apply E_Skip.
  -intros.
   assert(st1 = t_update st1 X (aeval st1 (AId X))).
   +simpl. apply functional_extensionality. intros.
    rewrite t_update_same. auto.
   +rewrite H0. simpl. inversion H. apply E_Ass. simpl. auto.
Qed.


Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros.
  unfold aequiv in H.
  unfold cequiv. split.
  -intros. assert(st1 = t_update st X (aeval st e)).
    *simpl in H. rewrite <- H. inversion H0. subst.
     apply functional_extensionality. intros.
     rewrite t_update_same. reflexivity.
    *subst. apply E_Ass. reflexivity.
  -intros. simpl in H. inversion H0. subst.
   rewrite <- H in H0. assert(st = t_update st X (aeval st e)).
   *rewrite <- H. apply functional_extensionality. intros.
    rewrite t_update_same. reflexivity.
   *rewrite <- H1. apply E_Skip.
   Show Proof.
Qed.







(*Properties of Behavioral Equivalence*)
(*---------------------------------------------------*)
(*
Behavioral Equivalence really are equivalences, that they are 
reflexive, symmetric, and transitive.
*)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros. unfold aequiv. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros. unfold aequiv in H. unfold aequiv. intros. 
  rewrite H. reflexivity.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  intros. unfold aequiv in H, H0. unfold aequiv.
  intros. rewrite H. apply H0.
Qed.




Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. 
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. 
Qed.





Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  intros.
  unfold cequiv.
  reflexivity.
Qed.


Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  intros. unfold cequiv in H. unfold cequiv.
  intros. rewrite H. reflexivity.
Qed.


Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  intros.
  unfold cequiv in *.
  intros. rewrite H. apply H0.
Qed.





(*
  Behavioral Equivalence Is a Congruence:

        aequiv a1 a1'
--------------------------------
  cequiv (i ::= a1) (i ::= a1')


        cequiv c1 c1'
        cequiv c2 c2'
--------------------------------
  cequiv (c1;;c2) (c1';;c2')

...and so on for the other forms of commands.
即一个program的subProgram可以替换为与之等价的subProgram，而整个
program也与原来等价。
they allow us to replace a small part of a large program 
with an equivalent small part and know that the whole large 
programs are equivalent without doing an explicit proof about 
the non-varying parts
*)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros.
  unfold cequiv. unfold aequiv in *.
  intros. split.
  -intros. inversion H0. subst. rewrite H. apply E_Ass. reflexivity.
  -intros. inversion H0. subst. rewrite <- H. apply E_Ass. reflexivity.
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  intros. unfold cequiv in *. unfold bequiv in *. split.
  -intros. remember (WHILE b1 DO c1 END) as cwhile eqn:Hw.
   induction H1; inversion Hw.
   +subst. clear Hw. apply E_WhileEnd. rewrite <- H. apply H1.
   +subst. clear Hw. apply E_WhileLoop with st1.
    *subst. rewrite <- H. apply H1.
    *rewrite <- H0. apply H1_.
    *apply IHceval2. reflexivity.
  -intros. remember (WHILE b1' DO c1' END) as cwhile eqn:Hw.
   induction H1; inversion Hw.
   +subst. clear Hw. apply E_WhileEnd. rewrite H. apply H1.
   +subst. clear Hw. apply E_WhileLoop with st1.
    *subst. rewrite H. apply H1.
    *rewrite H0. apply H1_.
    *apply IHceval2. reflexivity.
Qed.


Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold cequiv, bequiv. intros. split.
  -intros. inversion H2. subst.
    +apply E_IfTrue. 
      *rewrite <- H. assumption. 
      *rewrite <- H0. assumption.
    +subst. apply E_IfFalse.
      *rewrite <- H. assumption.
      *rewrite <- H1. assumption.
  -intros. inversion H2. subst.
    +apply E_IfTrue. 
      *rewrite H. assumption. 
      *rewrite H0. assumption.
    +subst. apply E_IfFalse.
      *rewrite H. assumption.
      *rewrite H1. assumption.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
Admitted.



(*example*)
Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X) (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
  -unfold cequiv. intros. reflexivity.
  -apply CIf_congruence.
    *unfold bequiv. intros. reflexivity.
    *apply CAss_congruence. unfold aequiv. simpl. intros. omega.
    *unfold cequiv. intros. reflexivity.
Qed.









(*Program Transformations*)
(*---------------------------------------------------*)
(*
A program transformation is a function that takes a program
as input and produces some variant of the program as output.

Compiler optimizations such as constant folding are a canonical 
example, but there are many others.

A program transformation is sound if it preserves the behavior
of the original program.
*)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).


(*The Constant-Folding Transformation*)
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. 
  reflexivity. 
Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if leb n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.


Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO c END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.


Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof.
  simpl. reflexivity.
Qed.







(*Soundness of Constant Folding*)
Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. unfold aequiv.
  intros. induction a; try(simpl; reflexivity);
  try(destruct (fold_constants_aexp a1) eqn:Hd; 
      destruct (fold_constants_aexp a2) eqn:Hd2;
      simpl; rewrite Hd; rewrite Hd2; rewrite IHa1; 
      rewrite IHa2; simpl; reflexivity).
Qed.


Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. unfold bequiv. intros.
  induction b; try(simpl; reflexivity).
  -rename a into a1. rename a0 into a2. simpl.
   remember (fold_constants_aexp a1) as a1'.
   remember (fold_constants_aexp a2) as a2'.
   replace (aeval st a1) with (aeval st a1').
   replace (aeval st a2) with (aeval st a2').
   try(destruct a1'; destruct a2');
    try(simpl; destruct (n =? n0);
        try(simpl; reflexivity));
    repeat try(simpl; reflexivity).
    *rewrite Heqa2'; rewrite <- fold_constants_aexp_sound; reflexivity.
    *rewrite Heqa1'; rewrite <- fold_constants_aexp_sound; reflexivity.
  -rename a into a1. rename a0 into a2. simpl.
   remember (fold_constants_aexp a1) as a1'.
   remember (fold_constants_aexp a2) as a2'.
   replace (aeval st a1) with (aeval st a1').
   replace (aeval st a2) with (aeval st a2').
   try(destruct a1'; destruct a2');
    try(simpl; destruct (n =? n0);
        try(simpl; reflexivity));
    repeat try(simpl; reflexivity).
    *destruct (n <=? n0). **simpl. reflexivity. **reflexivity.
    *destruct (n <=? n0). **simpl. reflexivity. **reflexivity.
    *rewrite Heqa2'; rewrite <- fold_constants_aexp_sound; reflexivity.
    *rewrite Heqa1'; rewrite <- fold_constants_aexp_sound; reflexivity.
  -simpl. rewrite IHb. destruct b;
   try(simpl; reflexivity).
Admitted.


Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    + (* b always true *)
      apply trans_cequiv with c1; try assumption. unfold cequiv.
      intros. split.
      *intros. inversion H0. subst. **assumption. **subst.
       unfold bequiv in H. rewrite H in H6. simpl in H6. inversion H6.
      *intros. apply E_IfTrue. **unfold bequiv in H. rewrite H. 
       simpl. reflexivity. **assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
Admitted.









(*Proving That Programs Are Not Equivalent*)
(*----------------------------------------------------------*)

(*把a中的i替换为u*)
Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId i' =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2 =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).


Theorem subst_inequiv :
  not subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  -subst. apply E_Seq with (t_update empty_state X 1).
    *apply E_Ass. simpl. reflexivity.
    *apply E_Ass. reflexivity.
  -subst. apply E_Seq with (t_update empty_state X 1).
    *apply E_Ass. reflexivity.
    *apply E_Ass. reflexivity.
  -subst. apply E_Seq with (t_update empty_state X 1).
    *apply E_Ass. reflexivity.
    *apply E_Ass. reflexivity.
  -unfold cequiv in *.
  apply H in H1.
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.
Qed.


Theorem inequiv_exercise:
  not (cequiv (WHILE BTrue DO SKIP END) SKIP).
Proof.
  unfold not.
  intros.
  unfold cequiv in *.
  remember (WHILE BTrue DO SKIP END) as Wc.
  remember (empty_state) as st.
  remember (t_update empty_state X 1) as st'.
  assert (SKIP / st \\ st).
  -apply E_Skip.
  -apply H in H0.  induction H0;
   try(subst; inversion HeqWc).
   *subst. inversion HeqWc. subst. simpl in H0. inversion H0.
   *subst. inversion HeqWc. subst. clear HeqWc H0. inversion H0_.
    subst. clear H0_. apply IHceval2.
    +reflexivity.
    +apply H.
    +reflexivity.
Qed.











(* Nondeterministic Imp *)
(*-------------------------------------------------------------*)
(*
The new command has the syntax HAVOC X, where X is an identifier.
The effect of executing HAVOC X is to assign an arbitrary number
to the variable X, nondeterministically.

In a sense, a variable on which we do HAVOC roughly corresponds 
to an unitialized variable in a low-level language like C
*)
Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com. (* <---- new *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (X: id) (n: nat) (st: state), 
      (HAVOC X) / st \\ (t_update st X n)

  where "c1 '/' st '\\' st'" := (ceval c1 st st').


Example havoc_example1 : (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
  apply E_Havoc.
Qed.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
  apply E_Seq with empty_state.
  -apply E_Skip. -apply E_Havoc.
Qed.


Definition cequiv (c1 c2 : com): Prop :=
  forall st st', c1 / st \\ st' <-> c2 / st \\ st'.


(* exercise *)
Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.


Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
Admitted.


Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.


Lemma p1_may_diverge : forall st st',   
  beval st (BNot (BEq (AId X) (ANum 0))) = true  ->
  ~ p1 / st \\ st'.
Proof.
Admitted.

End Himp.





















(*
  contents:
  1. behaviorally equivalent
  2.
  3.
  4.
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







(*---------------------------------------------------*)
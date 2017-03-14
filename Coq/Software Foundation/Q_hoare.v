(*
  contents:
  1. Assertion
    - Open Scope XX
  2. Hoare Triples
  3. Proof Rules (& eapply, eassumption )
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


(*
在equiv.v中我们讨论了imp的一些meta property。"meta" in the sense 
that they are properties of the language as a whole, rather 
than of particular programs in the language.

在本章中将讲一个 systematic method for reasoning about the correctness
of PARTICULAR programs in Imp
*)



(* Assertions *)
(*------------------------------------------------------------*)
(*
an assertion is just a family of propositions indexed by a state.
*)
Definition Assertion := state -> Prop.

(*example*)
Module ExAssertions.

Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

End ExAssertions.


(*
Given two assertions P and Q, we say that P implies Q, written 
P ->> Q, if, whenever P holds in some state st, Q also holds.
*)
Definition assert_implies (P Q: Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope. 


(* Open Scope XX *)
(*
The hoare_spec_scope annotation here tells Coq that this 
notation is not global but is intended to be used in particular
contexts. The Open Scope tells Coq that this file is one such 
context.
*)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.











(* Hoare Triples *)
(*------------------------------------------------------------*)
(*
If command c is started in a state satisfying assertion P, and if 
c eventually terminates in some final state, then this final 
state will satisfy the assertion Q.
Such a claim is called a Hoare Triple.
*)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
     c / st \\ st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


(*exercise*)
Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold hoare_triple.
  intros. apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  unfold not in *.
  apply H in H1.
  inversion H1.
Qed.










(* Proof Rules *)
(*------------------------------------------------------------*)
(*
we'll introduce a rule for reasoning about each of the different 
syntactic forms of commands in Imp. plus a couple of "structural" rules 
for gluing things together. We will then be able to prove programs 
correct using these proof rules, without ever unfolding the definition 
of hoare_triple.
*)


(* Assignment *)
(*
 Hoare rule for assignment:
      {{ P [X |-> a] }} X ::= a {{ Q }}
Since Q is an arbitrary Coq proposition, we can't directly "edit" its 
text. Instead, we can achieve the same effect by evaluating Q in an 
updated state:
*)

Definition assn_sub (X: id) (a: aexp) P : Assertion :=
  fun st => P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).
(*
assn_sub 实现了把P中的X替换为a的值的效果。
因为在st中追加了X的值a，这样只要访问X的地方
都会得到a的值。
*)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  intros.
  unfold hoare_triple.
  intros. unfold assn_sub in *.
  inversion H. subst. assumption.
Qed.


Example assn_sub_example :
  {{(fun st => st X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn.
Qed.

Example assn_sub_ex1 :
  {{ (fun st => st X <= 5) [X |-> (APlus (AId X) (ANum 1))]  }}
  X ::= (APlus (AId X) (ANum 1))
  {{ (fun st => st X <= 5) }}.
Proof.
  apply hoare_asgn.
Qed.

Example assn_sub_ex2 :
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> (ANum 3)]  }}
  X ::= (ANum 3)
  {{ (fun st => 0 <= st X /\ st X <= 5) }}.
Proof. apply hoare_asgn. 
Qed.

(*
hoare_asgn_fwd rule复杂不方便：

{{fun st ⇒ P st ∧ st X = m}}
    X ::= a
{{fun st ⇒ P st' ∧ st X = aeval st' a }}
(where st' = t_update st X m)

*)
Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y},
     (forall(x: X), f x = g x) -> f = g) ->
  forall m a P,

  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (t_update st X m) /\ st X = aeval (t_update st X m) a }}.
Proof.
  intros. unfold hoare_triple. intros. split.
  -inversion H0. inversion H1. subst. clear H1.
   assert (st =  (t_update
     (t_update st X (aeval st a)) X
     (st X))).
   +apply functional_extensionality. intros.
    Admitted.


(*
第二种forward rule:
{{fun st ⇒ P st}}
    X ::= a
{{fun st ⇒ ∃m, P (t_update st X m) ∧	st X = aeval (t_update st X m) a}}
*)
Theorem hoare_asgn_fwd_exists :
  forall X a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (t_update st X m) /\
                st X = aeval (t_update st X m) a }}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H. subst. exists (aeval st (AId X)).
  split.
  -assert (st = (t_update
     (t_update st X (aeval st a)) X
     (aeval st (AId X)))).
   +apply functional_extensionality. intros.
    Admitted.





(* Consequence * 3 *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold hoare_triple in *.
  unfold assert_implies in *.
  intros.
  apply H0 in H2.
  apply H in H1.
  -apply H1. -apply H2.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple in *.
  unfold assert_implies in *.
  intros.
  apply H in H1.
  -apply H0 in H1. apply H1.
  -apply H2.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros.
  apply hoare_consequence_pre with P'.
  -apply hoare_consequence_post with Q'.
   +assumption.
   +assumption.
  -assumption.
Qed.


Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre with 
    (P':=((fun st : state => st X = 1) [X |-> (ANum 1)])).
  -apply hoare_asgn.
  -unfold assn_sub. unfold t_update. simpl. unfold assert_implies.
   intros. reflexivity.
Qed.










(* eapply, eassumption *)
(*------------------------------------------------------------*)
(*
每次使用apply时需要手动用with指定元变量的具体值, This is annoying, both 
because the assertion is a bit long and also because, in 
hoare_asgn_example1, the very next thing we are going to do — 
applying the hoare_asgn rule — will tell us exactly what it should 
be! We can use eapply instead of apply to tell Coq, essentially, "Be 
patient: The missing part is going to be filled in later in the 
proof."
*)
Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assert_implies, assn_sub, t_update. intros. reflexivity.
Qed.


(*
Coq also provides an eassumption tactic that solves the goal if one 
of the premises matches the goal up to instantiations of existential 
variables.
*)
Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) 
                                  (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.













(* SKIP *)
(*------------------------------------------------------------*)
Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst. assumption.
Qed.













(* Sequencing *)
(*------------------------------------------------------------*)
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H1. subst.
  apply H0 in H5. apply H in H8.
  -assumption. -assumption. -assumption.
Qed.

(*
in the rule hoare_seq, the premises are given in backwards order (c2 
before c1). This matches the natural flow of information in many of 
the situations, since the natural way to construct a Hoare-logic 
proof is to begin at the end of the program (with the final 
postcondition) and push postconditions backwards through commands 
until we reach the beginning.
*)


Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a;; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros.
  eapply hoare_seq.
  -apply hoare_skip.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, assn_sub. intros.
    assumption.
Qed.


Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
  -apply hoare_asgn.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, assn_sub.
    intros.
    simpl.
    unfold t_update. simpl.
    auto.
Qed.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  Z ::= (AId X);;
  X ::= (AId Y);;
  Y ::= (AId Z)
  {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq.
  -eapply hoare_seq.
   +apply hoare_asgn.
   +apply hoare_asgn.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, assn_sub. simpl. intros.
    unfold t_update. simpl. assumption.
Qed.








(* Conditionals *)
(*------------------------------------------------------------*)
(*
      {{P ∧  b}} c1 {{Q}}
      {{P ∧ ~b}} c2 {{Q}}
------------------------------------
{{P}} IFB b THEN c1 ELSE c2 FI {{Q}}

P ∧ b, is the conjunction of an assertion and a boolean expression 
it doesn't well typed. To fix this, we need a way of formally change 
any bexp b to an assertion:
*)
Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros.
  unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> not ((bassn b) st).
Proof.
  unfold bassn, not.
  intros. rewrite H in H0. inversion H0.
Qed.


Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  unfold hoare_triple, bassn, not.
  intros. inversion H1. subst.
  -apply H in H9. assumption.
   +split. ++apply H2. ++apply H8.
  -subst. apply H0 in H9.
   +apply H9. 
   +split.
    ++apply H2.
    ++intros. rewrite H8 in H3. inversion H3.
Qed.


Example if_example :
    {{fun st => True}}
    IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
    FI
    {{fun st => st X <= st Y}}.
Proof.
  apply hoare_if.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, assn_sub. intros.
    simpl. unfold bassn in *. inversion H.
    simpl in H1. unfold t_update. simpl.
    apply beq_nat_true in H1. rewrite H1.
    auto.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, bassn, assn_sub. simpl.
    intros. unfold t_update. simpl. omega.
Qed.


Theorem if_minus_plus :
  {{fun st => True}}
    IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
    FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, assn_sub, bassn, t_update.
    simpl. intros. inversion H. apply leb_complete in H1.
    omega.
  -eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, assn_sub, bassn, t_update.
    simpl. intros. reflexivity.
Qed.





(* exercise: one side condition *)
Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.


Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).


Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ;; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_If1True : forall st st' b c,
                  beval st b = true ->
                  c / st || st' ->
                  (IF1 b THEN c FI) / st || st'
  | E_If1False : forall st b c,
                   beval st b = false ->
                   (IF1 b THEN c FI) / st || st
  where "c1 '/' st '||' st'" := (ceval c1 st st').

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.


Theorem hoare_if1 : forall P Q c b,
    (fun st => P st /\ ~(bassn b st)) ->> Q ->
    {{fun st => P st /\ bassn b st}} c {{Q}} ->
    {{P}} IF1 b THEN c FI {{Q}}.
Proof.
  unfold hoare_triple, assert_implies, bassn. intros.
  inversion H1. subst.
  -apply H0 in H8. +apply H8. +split; assumption.
  -subst.
   assert (P st' /\ beval st' b <> true).
   +split. *assumption. *rewrite H7. auto.
   +apply H in H3. assumption.
Qed.

End If1.








(* loops *)
(*------------------------------------------------------------*)
Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ not (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileEnd *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileLoop *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st1). assumption.
    split. assumption. apply bexp_eval_true. assumption.
Qed.


Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  -apply hoare_while.
   eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assn_sub, assert_implies, bassn.
    simpl. intros. inversion H. unfold t_update.
    simpl. apply leb_complete in H1. omega.
  -unfold assn_sub, assert_implies, bassn.
   simpl. intros. inversion H. destruct (st X <=? 2) eqn:Hx.
   +destruct H1. reflexivity.
   +apply leb_iff_conv in Hx. omega.
Qed.


Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros.
  eapply hoare_consequence_post.
  -apply hoare_while.
   eapply hoare_consequence_pre.
   +apply hoare_skip.
   +unfold assert_implies, bassn. simpl. intros. apply H.
  -unfold assert_implies, bassn. simpl. intros. inversion H.
   destruct H1. reflexivity.
Qed.
(*
this result is not surprising because the definition of 
hoare_triple asserts that the postcondition must hold only when 
the command terminates. If the command doesn't terminate, we can 
prove anything we like about the post-condition.
*)







(*exercise*)
(*------------------------------------------------------------*)
Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).


Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st \\ t_update st X n

  where "c1 '/' st '\\' st'" := (ceval c1 st st').


Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st \\ st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.


Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
  fun st => forall n, Q (t_update st X n).


Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  unfold hoare_triple, havoc_pre. intros.
  inversion H. subst. apply H0.
Qed.

End Himp.


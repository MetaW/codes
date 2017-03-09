(*
  contents:
  1. Assertion
    - Open Scope XX
  2. Hoare Triples
  3. Proof Rules (& eapply, eassumption )
  4.
  5.
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









(*------------------------------------------------------------*)
(*------------------------------------------------------------*)
(*------------------------------------------------------------*)
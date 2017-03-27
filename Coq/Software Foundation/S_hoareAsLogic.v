(*
  contents:
  1. define hoare rules as axioms
  2. hoare_proof_complete
*)


Require Import L_imp.
Require Import Q_hoare.


(* define hoare rules as axioms *)
Inductive hoare_proof : Assertion -> com -> Assertion -> Prop :=
| H_Skip    : forall P, hoare_proof P (SKIP) P
| H_Asgn    : forall Q V a,
                hoare_proof (assn_sub V a Q) (V ::= a) Q
| H_Seq     : forall P c Q d R,
                hoare_proof P c Q -> hoare_proof Q d R
                -> hoare_proof P (c;;d) R
| H_If      : forall P Q b c1 c2,
                hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
                hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
                hoare_proof P (IFB b THEN c1 ELSE c2 FI) Q
| H_While   : forall P b c,
                hoare_proof (fun st => P st /\ bassn b st) c P ->
                hoare_proof P (WHILE b DO c END) 
                            (fun st => P st /\ not (bassn b st))
| H_Consequence : forall (P Q P' Q' : Assertion) c,
                    hoare_proof P' c Q' ->
                    (forall st, P st -> P' st) ->
                    (forall st, Q' st -> Q st) ->
                    hoare_proof P c Q.

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  intros.
  apply H_Consequence with (P':=P') (Q':=Q).
  -assumption. -assumption. -intros. assumption.
Qed.


Lemma H_Consequence_post : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  intros.
  apply H_Consequence with (P':=P) (Q':=Q');
  try assumption. -intros. assumption.
Qed.

Example sample_proof :
  hoare_proof
    (assn_sub X (APlus (AId X) (ANum 1))
              (assn_sub X (APlus (AId X) (ANum 2))
                        (fun st => st X = 3) ))
    (X ::= APlus (AId X) (ANum 1);; (X ::= APlus (AId X) (ANum 2)))
    (fun st => st X = 3).
Proof.
  eapply H_Seq.
  -apply H_Asgn.
  -apply H_Asgn.
Qed.


Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  intros. induction H.
  -apply hoare_skip.
  -apply hoare_asgn.
  -subst. apply hoare_seq with (Q:=Q).
   +assumption. +assumption.
  -apply hoare_if. +assumption. +assumption.
  -apply hoare_while. assumption.
  -apply hoare_consequence with (P':=P') (Q':=Q').
   +assumption. 
   +unfold assert_implies. assumption.
   +unfold assert_implies. assumption.
Qed.



Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intros.
  induction c.
  -apply H_Consequence_post with (Q':=P). +apply H_Skip. +auto.
  -eapply H_Consequence_pre. +apply H_Asgn. +intros. unfold assn_sub. auto.
Admitted.



Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  intros.
  destruct H.
  inversion H.
Qed.




Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].


Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros.
  induction c.
  -pre_false_helper H_Skip.
  -pre_false_helper H_Asgn.
Admitted.













(* hoare_proof_complete *)
(*--------------------------------------------------------------------*)
Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', c / s \\ s' -> Q s'.

Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
Proof.
  intros.
  unfold wp, hoare_triple. intros.
  apply H0 in H. assumption.
Qed.

Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
Proof.
  unfold wp, hoare_triple. intros.
  apply H in H1; assumption.
Qed.


Lemma bassn_eval_false : forall b st, not (bassn b st) 
                                -> beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.


Theorem hoare_proof_complete: forall P c Q,
  {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c. intros.
  -eapply H_Consequence.
   +eapply H_Skip.
   +intros. eassumption.
   +intros. unfold hoare_triple in *. apply H with (st).
    *apply E_Skip. *assumption.
  -intros. eapply H_Consequence.
   +eapply H_Asgn.
   +intros. unfold hoare_triple in H. apply H with (st).
    *apply E_Ass. reflexivity. 
    *assumption.
   +intros. apply H0.
  -intros. apply H_Seq with (wp c2 Q).
   +eapply IHc1. unfold wp, hoare_triple in *. intros.
    apply H with (st).
    *apply E_Seq with (st'); assumption.
    *assumption.
   +eapply IHc2. apply wp_is_precondition.
  -intros. eapply H_If.
   +eapply IHc1. unfold hoare_triple in *.
    intros. apply H with (st). destruct H1.
    *eapply E_IfTrue.
     ++unfold bassn in *. assumption.
     ++assumption.
    *apply H1.
   +eapply IHc2. unfold hoare_triple in *.
    intros. apply H with (st). destruct H1.
    *eapply E_IfFalse.
     ++unfold not, bassn in H2. destruct (beval st b) eqn:Hx.
       **assert(true = true). 
         +++reflexivity. +++apply H2 in H3. inversion H3.
       **reflexivity.
     ++assumption.
    *apply H1.
  -intros.
   eapply H_Consequence with (P' := wp (WHILE b DO c END) Q).
   +apply H_While. apply IHc. intros st st' Ha H'.
    destruct H'. unfold wp in *. intros.
    apply H0. eapply E_WhileLoop.
    *assumption. *eassumption.
    *assumption.
   +apply wp_is_weakest. assumption.
   +simpl. intros. destruct H0.
    apply wp_is_precondition with (WHILE b DO c END) st.
    *apply E_WhileEnd. apply bassn_eval_false. assumption.
    *assumption.
Qed.



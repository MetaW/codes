(*
  contents:
  1. Decorated Programs
  2.
  3.
  4.
  5.
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import H_maps.
Require Import L_imp.
Require Import Q_hoare.





(* Decorated Programs *)
(*------------------------------------------------------------*)
(*
The beauty of Hoare Logic is that it is compositional: the 
structure of proofs exactly follows the structure of programs.

a decorated program consists of the program text interleaved with 
assertions (either a single assertion or possibly two assertions 
separated by an implication). To check that a decorated program 
represents a valid proof, we check that each individual command is 
locally consistent with its nearby assertions
*)

Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  -apply hoare_while.
   eapply hoare_consequence_pre.
   +apply hoare_asgn.
   +unfold assert_implies, bassn, assn_sub. simpl.
    intros. reflexivity.
  -unfold assert_implies, bassn, assn_sub. simpl.
   intros. inversion H. destruct (st X =? 0) eqn:Hx.
   apply beq_nat_true in Hx. assumption. simpl in H1.
   destruct H1. auto.
Qed.






(*Finding Loop Invariants*)
(*------------------------------------------------------------*)
(*
Once the outermost precondition and postcondition are chosen, 
the only creative part in verifying programs using Hoare Logic is 
finding the right loop invariants.

it must be weak enough to be implied by the loop's precondition
it must be strong enough to imply the program's postcondition
it must be preserved by one iteration of the loop

One way to find an invariant that satisfies these three 
conditions is by using an iterative process: start with a 
"candidate" invariant (a guess or a heuristic choice) and check 
the three conditions above; if any of the checks fails, try to 
use the information that we get from the failure to produce 
another candidate invariant, and repeat the process.

Very often, even if a variable is used in a loop in a read-only 
fashion, it is necessary to add to the loop invariant.
*)

(* exercise *)
Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  not (2 <= x) ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity. 
  simpl. exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros m.
  apply hoare_consequence_pre with 
    (P' := (fun st => parity m = parity (st X))).
  -eapply hoare_consequence_post.
   +apply hoare_while.
    eapply hoare_consequence_pre.
    *apply hoare_asgn.
    *unfold assert_implies, bassn, assn_sub. simpl.
     intros. destruct H. rewrite H. unfold t_update. simpl.
     destruct (st X) eqn:He.
     ++inversion H0.
     ++destruct n. ** inversion H0. **simpl. 
       rewrite <- minus_n_O. auto.
   +unfold assert_implies, bassn, assn_sub. simpl. intros.
    destruct H. rewrite H. destruct (st X) eqn:Hx.
    *simpl. reflexivity.
    *destruct n. ++auto. ++destruct H0. reflexivity.
  -unfold assert_implies, bassn, assn_sub. simpl. intros.
   rewrite H. reflexivity.
Qed.





(* weakest precondition *)
(*------------------------------------------------------------*)
Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).


Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp, hoare_triple, assert_implies. split.
  -intros. inversion H. subst. simpl. unfold t_update.
   simpl. omega.
  -intros. assert ((X ::= APlus (AId Y) (ANum 1)) / st \\ 
   (t_update st X (aeval st (APlus (AId Y) (ANum 1))))).
   +apply E_Ass. reflexivity.
   +apply H in H1.
    *simpl in *. unfold t_update in H1. simpl in *. omega.
    *assumption.
Qed.


Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp, assn_sub, hoare_triple, assert_implies. split.
  -intros. inversion H. subst. apply H0.
  -intros. assert ((X ::= a) / st \\ (t_update st X (aeval st a))).
   +apply E_Ass. reflexivity.
   +apply H in H1.
    *assumption.
    *assumption.
Qed.

Check hoare_if.

Theorem hoare_if_weakest : 
  forall (P : state -> Prop)
         (Q : Assertion) (b : bexp)
         (c1 c2 : com),
       is_wp (fun st : state =>
         P st /\ bassn b st) c1 Q ->
       is_wp (fun st : state =>
         P st /\ ~ bassn b st) c2 Q ->
       is_wp P (IFB b THEN c1 ELSE c2 FI) Q.
Proof.
  intros P Q b c1 c2. intros H1 H2.
  
  unfold is_wp. split.
  -unfold is_wp in *. destruct H1, H2. apply hoare_if.
   +assumption. +assumption.
  -destruct H1 , H2. 
Admitted.













(* Formal Decorated Programs *)
(*-----------------------------------------------------------*)
(*
The first thing we need to do is to formalize a variant of the 
syntax of commands with embedded assertions. We call the new 
commands decorated commands, or dcoms.
*)

Inductive dcom : Type :=
  | DCSkip : Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp -> Assertion -> dcom
  | DCIf : bexp -> Assertion -> dcom -> Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.


Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity) : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90) : dcom_scope.
      
Delimit Scope dcom_scope with dcom.
(*
we introduce these notations in a special scope called 
dcom_scope, and we wrap examples with the declaration % dcom to 
signal that we want the notations to be interpreted in this 
scope.
*)


Example dec_while : decorated := (
  {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0)))
  DO
    {{ fun st => True /\ st X <> 0}}
    X ::= (AMinus (AId X) (ANum 1))
    {{ fun _ => True }}
  END
  {{ fun st => True /\ st X = 0}} ->>
  {{ fun st => st X = 0 }}
) % dcom.

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _ => SKIP
  | DCSeq d1 d2 => (extract d1 ;; extract d2)
  | DCAsgn X a _ => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _ => WHILE b DO extract d END
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end.


Definition extract_dec (dec : decorated) : com :=
  match dec with 
  | Decorated P d => extract d
  end.


Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq d1 d2 => post d2
  | DCAsgn X a Q => Q
  | DCIf _ _ d1 _ d2 Q => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d => post d
  | DCPost c Q => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.





(* Extracting Verification Conditions *)
(*
The function verification_conditions takes a dcom d together with a 
precondition P and returns a proposition that, if it can be proved, 
implies that the triple {{P}} (extract d) {{post d}} is valid.
*)
Fixpoint verification_conditions (P : Assertion) (d:dcom)
                               : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
       verification_conditions P d1
    /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((fun st => P st /\ bassn b st) ->> P1)
      /\ ((fun st => P st /\ not (bassn b st)) ->> P2)
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial 
         precondition *)
      (P ->> post d)
      /\ ((fun st => post d st /\ bassn b st) ->> Pbody)
      /\ ((fun st => post d st /\ ~(bassn b st)) ->> Ppost)
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  induction d. intros. simpl in *.
  -eapply hoare_consequence_pre.
   +apply hoare_skip. +assumption.
  -simpl in *. intros. destruct H. apply IHd1 in H. apply IHd2 in H0.
   apply hoare_seq with (Q:=(post d1)).
   +assumption. +assumption.
  -intros. simpl in *. eapply hoare_consequence_pre.
   +apply hoare_asgn. +assumption.
  -intros. simpl in *. 
   destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]].
   apply IHd1 in HThen. apply IHd2 in HElse.
   apply hoare_if. 
   *apply hoare_consequence with (P':=a) (Q':=(post d1)).
    ++assumption. ++apply HPre1. ++assumption.
   *apply hoare_consequence with (P':=a0) (Q':=(post d2)).
    ++assumption. ++apply HPre2. ++assumption.
  -intros. simpl in *. destruct H. destruct H0. destruct H1.
   apply IHd in H2.
   apply hoare_consequence_pre with (P':=(post d)).
   apply hoare_consequence_post with 
         (Q':=(fun st => post d st /\ ~bassn b st)).
    *apply hoare_while.
     eapply hoare_consequence_pre.
     ++apply H2. ++assumption.
    *assumption.
    *assumption.
  -intros. simpl in *. destruct H. apply IHd in H0.
   eapply hoare_consequence_pre.
   +apply H0. +assumption.
  -intros. simpl in *. destruct H. apply IHd in H.
   eapply hoare_consequence_post.
   +apply H. +assumption.
Qed.


Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Lemma verification_correct_dec : forall dec,
  verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros [P d]. simpl. apply verification_correct.
Qed.











(* automation *)
(*-----------------------------------------------------------*)
(*
For very simple examples verify immediately solves the goal (provided 
that the annotations are correct).
*)
Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite t_update_eq;
  repeat (rewrite t_update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. 
  verify.
Qed.



Example subtract_slowly_dec (m:nat) (p:nat) : decorated := (
    {{ fun st => st X = m /\ st Z = p }} ->>
    {{ fun st => st Z - st X = p - m }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO   {{ fun st => st Z - st X = p - m /\ st X <> 0 }} ->>
       {{ fun st => (st Z - 1) - (st X - 1) = p - m }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => st Z - (st X - 1) = p - m }} ;;
     X ::= AMinus (AId X) (ANum 1)
       {{ fun st => st Z - st X = p - m }}
  END
    {{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
    {{ fun st => st Z = p - m }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. intros m p. verify. 
Qed.



(* Example *)
Definition swap : com :=
  X ::= APlus (AId X) (AId Y);;
  Y ::= AMinus (AId X) (AId Y);;
  X ::= AMinus (AId X) (AId Y).

Definition swap_dec m n : decorated :=
  ({{ fun st => st X = m /\ st Y = n}} ->>
   {{ fun st => (st X + st Y) - ((st X + st Y) - st Y) = n
                /\ (st X + st Y) - st Y = m }}
  X ::= APlus (AId X) (AId Y)
   {{ fun st => st X - (st X - st Y) = n /\ st X - st Y = m }};;
  Y ::= AMinus (AId X) (AId Y)
   {{ fun st => st X - st Y = n /\ st Y = m }};;
  X ::= AMinus (AId X) (AId Y)
   {{ fun st => st X = n /\ st Y = m}})%dcom.

Theorem swap_correct : forall m n,
  dec_correct (swap_dec m n).
Proof. 
intros; verify. 
Qed.


(*example*)
Definition if_minus_plus_com :=
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI.

Definition if_minus_plus_dec :=
  ({{fun st => True}}
  IFB (BLe (AId X) (AId Y)) THEN
      {{ fun st => True /\ st X <= st Y }} ->>
      {{ fun st => st Y = st X + (st Y - st X) }}
    Z ::= AMinus (AId Y) (AId X)
      {{ fun st => st Y = st X + st Z }}
  ELSE
      {{ fun st => True /\ ~(st X <= st Y) }} ->>
      {{ fun st => st X + st Z = st X + st Z }}
    Y ::= APlus (AId X) (AId Z)
      {{ fun st => st Y = st X + st Z }}
  FI
  {{fun st => st Y = st X + st Z}})%dcom.

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof. intros; verify. Qed.

Definition if_minus_dec :=
  ( {{fun st => True}}
  IFB (BLe (AId X) (AId Y)) THEN
      {{fun st => True /\ st X <= st Y }} ->>
      {{fun st => (st Y - st X) + st X = st Y
               \/ (st Y - st X) + st Y = st X}}
    Z ::= AMinus (AId Y) (AId X)
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  ELSE
      {{fun st => True /\ ~(st X <= st Y) }} ->>
      {{fun st => (st X - st Y) + st X = st Y
               \/ (st X - st Y) + st Y = st X}}
    Z ::= AMinus (AId X) (AId Y)
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  FI
    {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}})%dcom.

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof. verify. Qed.



(*example*)
Definition div_mod_dec (a b : nat) : decorated := (
{{ fun st => True }} ->>
  {{ fun st => b * 0 + a = a }}
  X ::= ANum a
  {{ fun st => b * 0 + st X = a }};;
  Y ::= ANum 0
  {{ fun st => b * st Y + st X = a }};;
  WHILE (BLe (ANum b) (AId X)) DO
    {{ fun st => b * st Y + st X = a /\ b <= st X }} ->>
    {{ fun st => b * (st Y + 1) + (st X - b) = a }}
    X ::= AMinus (AId X) (ANum b)
    {{ fun st => b * (st Y + 1) + st X = a }};;
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => b * st Y + st X = a }}
  END
  {{ fun st => b * st Y + st X = a /\ ~(b <= st X) }} ->>
  {{ fun st => b * st Y + st X = a /\ (st X < b) }}
)%dcom.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof. intros a b. verify.
  rewrite mult_plus_distr_l. omega.
Qed.


(*example*)
Definition find_parity : com :=
  WHILE (BLe (ANum 2) (AId X)) DO
     X ::= AMinus (AId X) (ANum 2)
  END.

(* 
There are actually several ways to phrase the loop invariant for
this program.  Here is one natural one, which leads to a rather
long proof: 
*)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Definition find_parity_dec m : decorated :=
  ({{ fun st => st X = m}} ->>
   {{ fun st => st X <= m /\ ev (m - st X) }}
  WHILE (BLe (ANum 2) (AId X)) DO
     {{ fun st => (st X <= m /\ ev (m - st X)) /\ 2 <= st X }} ->>
     {{ fun st => st X - 2 <= m /\ (ev (m - (st X - 2))) }}
     X ::= AMinus (AId X) (ANum 2)
     {{ fun st => st X <= m /\ ev (m - st X) }}
  END
   {{ fun st => (st X <= m /\ ev (m - st X)) /\ st X < 2 }} ->>
   {{ fun st => st X=0 <-> ev m }})%dcom.

Lemma l1 : forall m n p,
  p <= n ->
  n <= m ->
  m - (n - p) = m - n + p.
Proof. intros. omega. Qed.

Lemma l2 : forall m,
  ev m ->
  ev (m + 2).
Proof. intros. rewrite plus_comm. simpl. constructor. assumption. Qed.

Lemma l3' : forall m,
  ev m ->
  ~ev (S m).
Proof. induction m; intros H1 H2. inversion H2. apply IHm.
       inversion H2; subst; assumption. assumption. Qed.

Lemma l3 : forall m,
  1 <= m ->
  ev m ->
  ev (m - 1) ->
  False.
Proof. intros. apply l2 in H1.
       assert (G : m - 1 + 2 = S m). clear H0 H1. omega.
       rewrite G in H1. apply l3' in H0. apply H0. assumption. Qed.

Theorem find_parity_correct : forall m,
  dec_correct (find_parity_dec m).
Proof.
  intro m. verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (leb 2 (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; eauto; try omega.
    - (* invariant holds initially *)
      rewrite minus_diag. constructor.
    - (* invariant preserved *)
      rewrite l1; try assumption.
      apply l2; assumption.
    - (* invariant strong enough to imply conclusion 
         (-> direction) *)
      rewrite <- minus_n_O in H2. assumption.
    - (* invariant strong enough to imply conclusion
         (<- direction) *)
      destruct (st X) as [| [| n]]. 
      (* by H1 X can only be 0 or 1 *)
      + (* st X = 0 *)
        reflexivity.
      + (* st X = 1 *)
        apply l3 in H; try assumption. inversion H.
      + (* st X = 2 *)
        clear H0 H2. (* omega confused otherwise *)
        omega. 
Qed.

(* 
Here is a more intuitive way of writing the invariant: 
*)

Definition find_parity_dec' m : decorated :=
 ({{ fun st => st X = m}} ->>
  {{ fun st => ev (st X) <-> ev m }}
 WHILE (BLe (ANum 2) (AId X)) DO
    {{ fun st => (ev (st X) <-> ev m) /\ 2 <= st X }} ->>
    {{ fun st => (ev (st X - 2) <-> ev m) }}
    X ::= AMinus (AId X) (ANum 2)
    {{ fun st => (ev (st X) <-> ev m) }}
 END
 {{ fun st => (ev (st X) <-> ev m) /\ ~(2 <= st X) }} ->>
 {{ fun st => st X=0 <-> ev m }})%dcom.

Lemma l4 : forall m,
  2 <= m ->
  (ev (m - 2) <-> ev m).
Proof.
  induction m; intros. split; intro; constructor.
  destruct m. inversion H. inversion H1. simpl in *.
  rewrite <- minus_n_O in *. split; intro.
    constructor. assumption.
    inversion H0. assumption.
Qed.

Theorem find_parity_correct' : forall m,
  dec_correct (find_parity_dec' m).
Proof.
  intros m. verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (leb 2 (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; intuition; eauto; try omega.
  - (* invariant preserved (part 1) *)
    rewrite l4 in H0; eauto.
  - (* invariant preserved (part 2) *)
    rewrite l4; eauto.
  - (* invariant strong enough to imply conclusion 
       (-> direction) *)
    apply H0. constructor.
  - (* invariant strong enough to imply conclusion 
       (<- direction) *) 
      destruct (st X) as [| [| n]]. (* by H1 X can only be 0 or 1 *)
      + (* st X = 0 *)
        reflexivity.
      + (* st X = 1 *)
        inversion H.
      + (* st X = 2 *)
        clear H0 H H3. (* omega confused otherwise *) 
        omega.
Qed.

(* 
Here is the simplest invariant we've found for this program: 
*)

Definition parity_dec m : decorated :=
 ({{ fun st => st X = m}} ->> 
  {{ fun st => parity (st X) = parity m }}
 WHILE (BLe (ANum 2) (AId X)) DO
    {{ fun st => parity (st X) = parity m /\ 2 <= st X }} ->>
    {{ fun st => parity (st X - 2) = parity m }}
    X ::= AMinus (AId X) (ANum 2)
    {{ fun st => parity (st X) = parity m }}
 END
 {{ fun st => parity (st X) = parity m /\ ~(2 <= st X) }} ->>
 {{ fun st => st X = parity m }})%dcom.

Theorem parity_dec_correct : forall m,
  dec_correct (parity_dec m).
Proof.
  intros. verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (leb 2 (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; eauto; try omega.
  - (* invariant preserved *)
    rewrite <- H. apply parity_ge_2. assumption.
  - (* invariant strong enough *)
    rewrite <- H. symmetry. apply parity_lt_2. assumption.
Qed.



(*example*)
Definition sqrt_dec m : decorated := (
    {{ fun st => st X = m }} ->>
    {{ fun st => st X = m /\ 0*0 <= m }}
  Z ::= ANum 0
    {{ fun st => st X = m /\ st Z*st Z <= m }};;
  WHILE BLe (AMult (APlus (AId Z) (ANum 1))
                   (APlus (AId Z) (ANum 1)))
            (AId X) DO
      {{ fun st => (st X = m /\ st Z*st Z<=m)
                   /\ (st Z + 1)*(st Z + 1) <= st X }} ->>
      {{ fun st => st X = m /\ (st Z+1)*(st Z+1)<=m }}
    Z ::= APlus (AId Z) (ANum 1)
      {{ fun st => st X = m /\ st Z*st Z<=m }}
  END
    {{ fun st => (st X = m /\ st Z*st Z<=m)
                   /\ ~((st Z + 1)*(st Z + 1) <= st X) }} ->>
    {{ fun st => st Z*st Z<=m /\ m<(st Z+1)*(st Z+1) }})%dcom.

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. intro m. verify. Qed.




(*example*)
(* 
Again, there are several ways of annotating the squaring program.
The simplest variant we've found, [square_simpler_dec], is given
last. 
*)

Definition square_dec (m : nat) : decorated := (
  {{ fun st => st X = m }}
  Y ::= AId X
  {{ fun st => st X = m /\ st Y = m }};;
  Z ::= ANum 0
  {{ fun st => st X = m /\ st Y = m /\ st Z = 0}} ->>
  {{ fun st => st Z + st X * st Y = m * m }};;
  WHILE BNot (BEq (AId Y) (ANum 0)) DO
    {{ fun st => st Z + st X * st Y = m * m /\ st Y <> 0 }} ->>
    {{ fun st => (st Z + st X) + st X * (st Y - 1) = m * m }}
    Z ::= APlus (AId Z) (AId X)
    {{ fun st => st Z + st X * (st Y - 1) = m * m }};;
    Y ::= AMinus (AId Y) (ANum 1)
    {{ fun st => st Z + st X * st Y = m * m }}
  END
  {{ fun st => st Z + st X * st Y = m * m /\ st Y = 0 }} ->>
  {{ fun st => st Z = m * m }}
)%dcom.

Theorem square_dec_correct : forall m,
  dec_correct (square_dec m).
Proof.
  intro n. verify.
  - (* invariant preserved *)
    destruct (st Y) as [| y']. apply False_ind. apply H0.
    reflexivity.
    simpl. rewrite <- minus_n_O.
    assert (G : forall n m, n * S m = n + n * m). {
      clear. intros. induction n. reflexivity. simpl.
      rewrite IHn. omega. }
    rewrite <- H. rewrite G. rewrite plus_assoc. reflexivity.
Qed.

Definition square_dec' (n : nat) : decorated := (
  {{ fun st => True }}
  X ::= ANum n
  {{ fun st => st X = n }};;
  Y ::= AId X
  {{ fun st => st X = n /\ st Y = n }};;
  Z ::= ANum 0
  {{ fun st => st X = n /\ st Y = n /\ st Z = 0 }} ->>
  {{ fun st => st Z = st X * (st X - st Y)
               /\ st X = n /\ st Y <= st X }};;
  WHILE BNot (BEq (AId Y) (ANum 0)) DO
    {{ fun st => (st Z = st X * (st X - st Y) 
                /\ st X = n /\ st Y <= st X)
                 /\ st Y <> 0 }}
    Z ::= APlus (AId Z) (AId X)
    {{ fun st => st Z = st X * (st X - (st Y - 1))
                 /\ st X = n /\ st Y <= st X }};;
    Y ::= AMinus (AId Y) (ANum 1)
    {{ fun st => st Z = st X * (st X - st Y)
                 /\ st X = n /\ st Y <= st X }}
  END
  {{ fun st => (st Z = st X * (st X - st Y) 
              /\ st X = n /\ st Y <= st X)
               /\ st Y = 0 }} ->>
  {{ fun st => st Z = n * n }}
)%dcom.

Theorem square_dec'_correct : forall n,
  dec_correct (square_dec' n).
Proof.
  intro n. verify.
  - (* invariant holds initially *)
    rewrite minus_diag. omega.
  - (* invariant preserved *) subst.
    rewrite mult_minus_distr_l.
    repeat rewrite mult_minus_distr_l. rewrite mult_1_r.
    assert (G : forall n m p, 
                  m <= n -> p <= m -> n - (m - p) = n - m + p).
      intros. omega.
    rewrite G. reflexivity. apply mult_le_compat_l. assumption.
    destruct (st Y). apply False_ind. apply H0. reflexivity.
      clear. rewrite mult_succ_r. rewrite plus_comm.
      apply le_plus_l.
  - (* invariant + negation of guard imply 
       desired postcondition *)
    rewrite <- minus_n_O. reflexivity.
Qed.

Definition square_simpler_dec (m : nat) : decorated := (
  {{ fun st => st X = m }} ->>
  {{ fun st => 0 = 0*m /\ st X = m }}
  Y ::= ANum 0
  {{ fun st => 0 = (st Y)*m /\ st X = m }};;
  Z ::= ANum 0
  {{ fun st => st Z = (st Y)*m /\ st X = m }}->>
  {{ fun st => st Z = (st Y)*m /\ st X = m }};;
  WHILE BNot (BEq (AId Y) (AId X)) DO
    {{ fun st => (st Z = (st Y)*m /\ st X = m)
        /\ st Y <> st X }} ->>
    {{ fun st => st Z + st X = ((st Y) + 1)*m /\ st X = m }}
    Z ::= APlus (AId Z) (AId X)
    {{ fun st => st Z = ((st Y) + 1)*m /\ st X = m }};;
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => st Z = (st Y)*m /\ st X = m }}
  END
  {{ fun st => (st Z = (st Y)*m /\ st X = m) /\ st Y = st X }} ->>
  {{ fun st => st Z = m*m }}
)%dcom.

Theorem square_simpler_dec_correct : forall m,
  dec_correct (square_simpler_dec m).
Proof.
  intro m. verify.
  rewrite mult_plus_distr_r. simpl. rewrite <- plus_n_O.
  reflexivity.
Qed.



(*example*)
Definition two_loops_dec (a b c : nat) : decorated :=
( {{ fun st => True }} ->>
  {{ fun st => c = 0 + c /\ 0 = 0 }}
  X ::= ANum 0
  {{ fun st => c = st X + c /\ 0 = 0 }};;
  Y ::= ANum 0
  {{ fun st => c = st X + c /\ st Y = 0 }};;
  Z ::= ANum c
  {{ fun st => st Z = st X + c /\ st Y = 0 }};;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    {{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X <> a }} ->>
    {{ fun st => st Z + 1 = st X + 1 + c /\ st Y = 0 }}
    X ::= APlus (AId X) (ANum 1)
    {{ fun st => st Z + 1 = st X + c /\ st Y = 0 }};;
    Z ::= APlus (AId Z) (ANum 1)
    {{ fun st => st Z = st X + c /\ st Y = 0 }}
  END
  {{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X = a }} ->>
  {{ fun st => st Z = a + st Y + c }};;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    {{ fun st => st Z = a + st Y + c /\ st Y <> b }} ->>
    {{ fun st => st Z + 1 = a + st Y + 1 + c }}
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => st Z + 1 = a + st Y + c }};;
    Z ::= APlus (AId Z) (ANum 1)
    {{ fun st => st Z = a + st Y + c }}
  END
  {{ fun st => (st Z = a + st Y + c) /\ st Y = b }} ->>
  {{ fun st => st Z = a + b + c }}
)%dcom.

Theorem two_loops_correct : forall a b c,
  dec_correct (two_loops_dec a b c).
Proof. intros a b c. verify. Qed.



(*example*)

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Definition dpow2_down n :=
( {{ fun st => True }} ->>
  {{ fun st => 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 0 }}
  X ::= ANum 0
  {{ fun st => 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 (st X) }};;
  Y ::= ANum 1
  {{ fun st => st Y = (pow2 (st X + 1))-1 /\ 1 = pow2 (st X) }};;
  Z ::= ANum 1
  {{ fun st => st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X) }};;
  WHILE BNot (BEq (AId X) (ANum n)) DO
    {{ fun st => (st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X))
                 /\ st X <> n }} ->>
    {{ fun st => st Y + 2 * st Z = (pow2 (st X + 2))-1
                 /\ 2 * st Z = pow2 (st X + 1) }}
    Z ::= AMult (ANum 2) (AId Z)
    {{ fun st => st Y + st Z = (pow2 (st X + 2))-1
                 /\ st Z = pow2 (st X + 1) }};;
    Y ::= APlus (AId Y) (AId Z)
    {{ fun st => st Y = (pow2 (st X + 2))-1
                 /\ st Z = pow2 (st X + 1) }};;
    X ::= APlus (AId X) (ANum 1)
    {{ fun st => st Y = (pow2 (st X + 1))-1
                 /\ st Z = pow2 (st X) }}
  END
  {{ fun st => (st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X))
               /\ st X = n }} ->>
  {{ fun st => st Y = pow2 (n+1) - 1 }}
)%dcom.

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof. induction n; simpl. reflexivity. omega. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. induction n. simpl. constructor. simpl. omega. Qed.

Theorem dpow2_down_correct : forall n,
  dec_correct (dpow2_down n).
Proof.
  intro m. verify.
  - (* 1 *)
    rewrite pow2_plus_1. rewrite <- H0. reflexivity.
  - (* 2 *)
    rewrite <- plus_n_O.
    rewrite <- pow2_plus_1. remember (st X) as n.
    replace (pow2 (n + 1) - 1 + pow2 (n + 1))
       with (pow2 (n + 1) + pow2 (n + 1) - 1) by omega.
    rewrite <- pow2_plus_1.
    replace (n + 1 + 1) with (n + 2) by omega.
    reflexivity.
  - (* 3 *)
    rewrite <- plus_n_O. rewrite <- pow2_plus_1.
    reflexivity.
  - (* 4 *)
    replace (st X + 1 + 1) with (st X + 2) by omega.
    reflexivity.
Qed.


(*example*)
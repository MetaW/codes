(*
    content:
    1. Curry Howard Correspondence
    2. Print proof object
    3. 使用Definition手动构造Theorem
    4. Quantifiers, Implications, Functions
    5. 用tactics来生成程序
    6. Logical Connectives as Inductive Types
      (逻辑连接词即evidence constructor)
      - conjunction:/\ 的定义
      - disjunction \/ 的定义
      - Existential Quantification的定义
      - 区分类型与程序!!!
      - True & False 的定义
      - Equality的定义
*)
Require Import G_IndProp.

(* Curry Howard Correspondence *)
(*----------------------------------------------------*)
(*
    Inductive is used to declare both data types and propositions;
    -> is used both to describe the type of functions on data and 
    logical implication.
    
    This is not just a syntactic accident!
    programs and proofs in Coq are almost the same thing.

    命题就是类型，证明就是能够产生该类型的值的程序。
    AST就是证明树。

    A : B 
    A has a type of B
    A is a proof of B
    
    program   ---   type
    proof     ---   proposition
    evidence  ---   fact
*)






(* Print proof object *)
(*----------------------------------------------------*)
Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_O.
Qed.

Print ev_4.
(*
ev_4 = ev_SS 2 (ev_SS 0 ev_O)
     : ev 4

*)
Check ev_SS 2 (ev_SS 0 ev_O).  (* ev 4 *)

(*
ev_4的值就是ev_SS 2 (ev_SS 0 ev_O), 类型就是ev 4
*)




(* 使用Definition手动构造Theorem *)
(*----------------------------------------------------*)
(*
  When Coq is following a proof script, what is happening 
  internally is that it is gradually constructing a proof 
  object — a term whose type is the proposition being proved. 
  The tactics between Proof and Qed tell it how to build up a 
  term of the required type.

  Show Proof command to display the current state of the proof 
  tree at various points in the following tactic proof.
  eg:
*)

Theorem ev_4' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_O.
  Show Proof.
Qed.
(*
  At any given moment, Coq has constructed a term with a
 "hole" (indicated by ?Goal here, and so on), and it knows 
  what type of evidence is needed to fill this hole.
  Each hole corresponds to a subgoal, and the proof is 
  finished when there are no more subgoals.
*)




(*
  tactic proof只是为了方便构造目标类型(命题)的程序,它们不是必须的，
  实际上，我们总是能够使用Definition代替Theorem，并通过手动构造程序
  来得到一个特定类型的程序(evidence)。
  eg:
*)
Definition ev_4'' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_O).


(* Exercise *)
Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_O.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_O))).

(*
In Coq's computational universe where data structures and programs 
live, there are two sorts of values with arrows in their types:
constructors introduced by Inductively defined data types, and 
functions.
Similarly, in Coq's logical universe where we carry out proofs,
there are two ways of giving evidence for an implication:
constructors introduced by Inductively defined propositions, 
and functions!
*)






(* Quantifiers, Implications, Functions *)
(*----------------------------------------------------*)
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H.
  Show Proof.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.


(* the same as: *)
Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n:nat) => fun (H:ev n) => ev_SS (S (S n)) (ev_SS n H).

(* the same as: *)
Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

(*
the type of H, dependent on the value of n, this is Dependent Type.
-> and ∀ are really the same thing: -> is just a shorthand for 
a degenerate use of ∀ where there is no dependency. (∀ is a generalized
version of ->).

In dependent type, some type may need the value of other types,
they need to access the name of thoes types, so we use forall 
instead of ->.
*)

(*  !!!IMPORTANT!!!: *)
(*
  In general, "P → Q" is just syntactic sugar for "∀ (_:P), Q".
*)






(* 用tactics来生成程序 *)
(*----------------------------------------------------*)
(*
  我们能够手写term来构造一个命题(类型)的证明(程序)，同理我们也能通过
  proof tactic来构造一个程序instead of手写term.
*)
Definition add1 : nat -> nat.
Proof.
  intros n.
  Show Proof.
  apply S.
  Show Proof.
  apply n.
Defined.
(* Qed-defined objects are opaque during computation, Defined 
end onjects are transparent, This feature is mainly useful for 
writing functions with dependent types*)



Print add1.
(*
add1 = 
fun n : nat => S n
     : nat -> nat
*)

Compute add1 2. (* =3 : nat *) 








(* Logical Connectives as Inductive Types *)
(*----------------------------------------------------*)




(* conjunction:/\ 的定义 *)
Module Props.
Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.
End Props.

(*
split tactic actually works for any inductively 
defined proposition with only one constructor.
*)

Lemma and_comm : forall (P Q :Prop), P /\ Q <-> Q /\ P.
Proof.
  intros.
  split.
  -intros. split.
    +apply H.
    +apply H.
  -intros. split.
    +apply H.
    +apply H.
Qed.
Print and_comm.

(* write proofobject(program) by hand *)
Definition and_comm'_anx (P Q:Prop) (H : P /\ Q) :=
match H with
| conj p q => conj q p
end.


Definition and_comm' (P Q:Prop) : P /\ Q <-> Q /\ P :=
conj (and_comm'_anx P Q) (and_comm'_anx Q P).


(* exercise *)
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R:Prop) (H1: P/\Q) (H2: Q /\ R) =>
    match H1 with
    | conj p q => match H2 with
                  | conj q r => conj p r
                  end
    end.

Check conj_fact.






(* disjunction \/ 的定义 *)
Module Or.
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.
End Or.

(* exercise *)
Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q (H : P\/Q) => 
    match H with
    | or_introl p => or_intror p
    | or_intror q => or_introl q
    end.

Check or_comm.






(* Existential Quantification的定义 *)
Module Ex.
Inductive ex {A:Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x:A, P x -> ex P.

End Ex.







(* 区分类型与程序!!! *)
(*
  Dependent Type 给类型和程序之间的区分带来了一定难度，
  一定要区分开它们，eg: 前面定义的and, or, ex是用来构造
  类型的,而conj,or_introl,ex_intro是用来构造程序的。
  
  最后:函数不一定构造的就是程序,它既可以构造程序也能构造类型:
  fun x => x + 1    //这是程序
  fun x => ev x     //这是类型！！！
  因为函数体ev x是类型，而x+1是程序
  主要看函数体是类型构造子还是值构造子(evidence constructor)
  
  另外：只有函数构造的是程序的情况下，
  fun x:T =>... 的类型才是 forall x:T,...
  eg:
  Check fun x:nat => eq_refl x.   类型为forall x : nat, x = x  (eq_refl是值构造子)
  Check fun x:nat => x = x.       类型为nat -> Prop  (=是类型构造子:eq)
*)


(*所以
  exists x, P x       //类型
  去糖之后是:
  ex (fun x => P x)   //类型
*)

Check ex_intro.

(* exercise *)
Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_O)).

Print some_nat_is_even.

Check ex_intro.
Definition ex_ev_sn : ex (fun n => ev (S n)) :=
(ex_intro (fun n : nat => ev (S n)) 
          3
          (ev_SS 2 (ev_SS 0 ev_O))).

Check (fun n : nat => ev (S n)).






(* True & False *)
Module TF.
Inductive True : Prop :=
| I : True.

Inductive False : Prop:=.

(*False is an inductive type with no constructors, so no way 
to build evidence for it.*)
End TF.







(* Equality *)
Module MyEq.
Inductive eq {X : Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y) 
                    (at level 70, no associativity)
                    : type_scope.
End MyEq.


Lemma leibniz_equality : 
  forall (X:Type) (x y : X), x = y -> (forall P:X->Prop, P x -> P y).
Proof.
  intros.
  destruct H.
  apply H0.
  Show Proof.
Qed.


Lemma four : 2 + 2 = 3 + 1.
Proof.
  apply eq_refl.
  Show Proof.
Qed.

(*
The reflexivity tactic that we have used to prove equalities 
up to now is essentially just short-hand for apply refl_equal.
*)

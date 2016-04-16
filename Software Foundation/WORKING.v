(*
	包含：
	1.
	2.
	3.
*)

Require Export lists.

(*polymorphism*)
(*#####################################################*)
(*

*)

(*上一节我们建立了nat的list，然而我们需要更多种list*)
(* boollist *)
Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(*但这样很麻烦，我们不仅需要定义每个类型的list还要为其分别定义相应函数*)

(*下面定义一个范型的list解决这个问题*)
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(*现在list是一个类型到类型的函数*)
Check nil nat.
Check cons.

Check cons nat 1 (cons nat 4  (nil nat)) .


Check cons nat 3.
Check boollist.
Check nil Set.

Check cons Set nat (cons Set bool (nil Set)).


Fixpoint repeat X x n:=
  match n with
  | O => nil X
  | S n' => cons X x (repeat X x n')
  end.

Check repeat.


Example test_repeat1: 
	repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
  
  simpl.
  reflexivity.
Qed.

Example test_repeat2: 
	repeat bool false 1 = cons bool false (nil bool).

  simpl.
  reflexivity.
Qed.


(*Coq支持类型推导，与Haskell类似，如果Coq能够根据具体的函数实现
  推导出参数或函数返回值的类型，那么就可以省去不写，但为了使代码更
  易读，最好还是将类型写全。	
*)
(* eg: *)
Fixpoint repeat' X x n :=
  match n with
  | O => nil X
  | S n' => cons X x (repeat X x n')
  end.




Definition list123 :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).



Check nil.
Arguments nil {X}.
Check nil.

Arguments cons {X} _ _.
Check cons .

Arguments repeat {X} _ _.
Definition list222 := repeat 2 3.
Compute list222.

Fixpoint repeat2 {X:Type} (x:X) (n:nat):list X :=
  match n with
  | O => nil
  | S n' => cons x ( repeat2 x n')
  end.

Check repeat2.
Definition list333 := repeat2 3 3.
Compute list333.


Inductive list' {X:Type} : Type :=		(*这样才是定义多态的最简洁的方法，它从最开始就省去了*)
  | nil' : list'						(*冗余的参数，使后面的所有定义都简洁了*)
  | cons' : X -> list' -> list'.

Fixpoint repeat_for_list' (x:nat) (n:nat) :=
  match n with
  | O => nil'
  | S n' => cons' x (repeat_for_list' x n')
  end.

Check nil'.


Fixpoint app {X:Type} (l1 l2:list X):list X :=
  match l1 with
  | nil => l2
  | cons x l1' => cons x (app l1' l2) 
  end.

Fixpoint rev {X:Type} (l:list X):list X :=
  match l with
  | nil => nil
  | cons x m => app (rev m) (cons x nil) 
  end.

Fixpoint length {X:Type} (l:list X):nat :=
  match l with
  | nil => O
  | cons h t => 1 + (length t)
  end.



Fail Definition mynil := nil.

Check @nil nat.

Notation "x : y" := (cons x y)
  (at level 60, right associativity).

Notation "[]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

Notation "x ++ y" := (app x y)
  (at level 60, right associativity).



Theorem app_nil_r : 
	forall (X:Type) (l:list X), l ++ [] = l.
  
  intros X l.
  induction l.
    -reflexivity.
    -simpl.
     rewrite -> IHl.
     reflexivity.
Qed.

  
Theorem app_assoc : 
	forall (X:Type) (l m n:list X), l ++ m ++ n = (l ++ m) ++ n.

  intros X l m n.
  induction l.
    -simpl. auto.
    -simpl.
     rewrite -> IHl.
     auto.
Qed.


Theorem app_length : 
	forall (X:Type) (n m:list X), length (n ++ m) = (length n) + (length m).

  intros X n m.
  induction n.
    -simpl. auto.
    -simpl.
     rewrite IHn.
     auto.
Qed.

Theorem rev_app_distr : 
	forall (X:Type) (l1 l2:list X), rev (l1 ++ l2) = rev l2 ++ rev l1.

  intros X l1 l2.
  induction l1.
    -simpl. rewrite app_nil_r. auto.
    -simpl.
     rewrite IHl1.
     rewrite app_assoc.
     auto.
Qed.

Theorem rev_rev_app:
  forall (X:Type) (x:X) (l:list X), rev ((rev l) ++ [x]) = x:rev (rev l).

  intros.
  induction l as [| e l'].
    -simpl. auto.
    -simpl.
     rewrite rev_app_distr.
     simpl.
     reflexivity.
Qed. 

Theorem rev_involutive : 
	forall (X:Type) (l:list X), rev (rev l) = l.

  intros.
  induction l.
    -simpl. auto.
    -simpl.
     rewrite rev_rev_app.
     rewrite IHl.
     reflexivity.
Qed.

























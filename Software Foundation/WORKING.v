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

Inductive prod (X Y:Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).


(*下面定义函数*)
Fixpoint fst {X Y:Type} (p: prod X Y):X :=
  match p with
  | (x,y) => x
  end.

Fixpoint snd {X Y:Type} (p: prod X Y):Y :=
  match p with
  | (x,y) => y
  end.


Fixpoint combine {X Y:Type} (l1 :list X) (l2 :list Y):list (prod X Y) :=
  match l1,l2 with
  | [],_ => []
  | _,[] => []
  | x:xl,y:yl => (x,y):(combine xl yl)
  end.


Check @combine.
Compute (combine [1,2] [false,false,true,true]).



 Fixpoint unzip {X Y:Type} (l:list (prod X Y)):prod (list X) (list Y) :=
   match l with
   | [] => ([],[])
   | x:xl => ((fst x):fst (unzip xl), (snd x):snd (unzip xl))
   end.




Inductive option (X:Type) : Type :=
  | none : option X
  | some : X -> option X.

Arguments none {X}.
Arguments some {X} _.

(*下面我们实现list的nth_error函数*)
Fixpoint nth_error {X:Type} (l:list X) (n:nat):option X :=
  match n,l with
  | _,[] => none
  | O,x:xl => some x
  | S n',x:xl => nth_error xl n'
  end.

Compute (nth_error (@nil nat) 0).




Definition hd_error {X:Type} (l:list X):option X :=
  match l with
  | [] => none
  | x:xl => some x
  end.


Check @hd_error.

Compute hd_error (@nil nat).


Definition doit3times {X:Type} (f:X -> X) (x:X) :X :=
  f (f (f x)).


Example test_doit3times: 
  doit3times minustwo 9 = 3.

  auto.
Qed.


Fixpoint filter {X:Type} (f:X -> bool) (l:list X):list X :=
  match l with
  | [] => []
  | x:xl => match f x with
            | true => x:(filter f xl)
            | false => filter f xl
            end
  end.

Example test_filter: 
  filter evenb [1,2,3,4,5,6] = [2,4,6].
  
  simpl.
  auto.
Qed.

SearchAbout evenb.


Example test_doit3times2:
  doit3times (fun x:nat => x * x) 2 = 256.

  reflexivity.
Qed.

SearchAbout nat.

Fixpoint natltb (x y:nat) :bool :=
  match x,y with
  | O,O => false
  | O,S y' => false
  | S x',O => true
  | S x',S y' => natltb x' y'
  end.



Definition filter_even_gt7 (l:list nat): list nat :=
  filter (fun x => andb (evenb x) (natltb x 7)) l.

Example test_filter_even_gt7: 
  filter_even_gt7 [2,3,4,7,8,9,12] = [8,12].
  
  reflexivity.
Qed.


Fixpoint partition {X:Type} (f:X -> bool) (l:list X): prod (list X) (list X) :=
  match l with
  | [] => ([],[])
  | x:xl => if f x then (x:fst (partition f xl), snd (partition f xl))
                   else (fst (partition f xl), x:snd (partition f xl))
  end.




Example test_partition: 
  partition evenb [1,2,3,4,5] = ([2,4],[1,3,5]).

  reflexivity.
Qed.

Example test_partition2: 
  partition (fun x => false) [5,9,0] = ([],[5,9,0]).

  reflexivity.
Qed.


Fixpoint map {X Y:Type} (f: X -> Y) (l:list X): list Y :=
  match l with
  | [] => []
  | x:xl => (f x):(map f xl)
  end.


Fixpoint fold {X Y:Type} (f:X -> Y -> Y) (l:list X) (e:Y): Y :=
  match l with
  | [] => e
  | x:xl => f x (fold f xl e)
  end.

Check @fold.

Compute fold mult [1,2,3,4] .

Example fold_test1: 
  fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_test2: 
  fold andb [true,false,true,true] true = false.
Proof. reflexivity. Qed.

Example fold_test3: 
  fold app [[1,2],[],[3,4,5]] [] = [1,2,3,4,5].
Proof. reflexivity. Qed.


Check plus 3.

Fixpoint plusx (x:nat): nat -> nat :=
  fun t:nat => t + x.
Compute plusx 3 4.

Definition plusx2 (x:nat): nat -> nat := 
  plus x.

Definition plusx3 := plus 5.





(*
	包含：
	1.
	2.
	3.
*)

Require Export lists.

(*polymorphism 多态*)
(*#####################################################*)
(*

*)

(*上一节我们建立了nat的list，然而我们需要更多种list*)
(* boollist *)
Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(*但这样很麻烦，我们不仅需要定义每个类型的list还要为其分别定义相应函数*)

(*下面定义一个多态的list解决这个问题*)
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
(*
	现在list是一个类型到类型的函数,list,nil与cons的类型分别为
	list: Type -> Type.
	nil: forall X:Type, list X.
	cons forall X:Type, x -> list X -> list X.
	可以看出list是个函数，nil,cons是多态的constructors
		所以nil与cons用的时候要附加一个参数来确定x的具体类型
*)
(*eg:
Check nil.					:forall X:Type, list X
Check nil nat. 				:list nat
Check cons.					:forall X:Type, x -> list X -> list X
Check cons nat. 			:nat -> list nat -> list nat
Check cons nat 3.			:list nat -> list nat
Check cons nat 3 (nil nat).	:list nat

		Type 
		 |
		Set
		 |
	nat  bool   boollist ...

Check cons Set nat (cons Set bool (nil Set)).
*)

(*下面定义一些函数*)

Fixpoint repeat (X:Type) (x:X) (n:nat):list X:=
  match n with
  | O => nil X
  | S n' => cons X x (repeat X x n')
  end.

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
(*Check一下repeat'会发现它与上面的repeat的类型一模一样*)

(*自动类型推导还能作更多的事*)
(* eg: *)
Definition list123 :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
(*在这里可以不用一遍遍写类型，可以用"_"代替它，Coq可以根据表达式本身推出类型*)





(*这样还是太麻烦，代码冗长，一些方法可以减少不必要的参数*)
(*减少非必要参数的方法###############################################*)

(*---Way1:---(更方便)*)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} _ _.
(*Arguments将后面的名称的参数中能够自动推导出的放在{}中，这样的参数一般为类型，
这样这些名称使用时可以只写剩下的参数了，eg:  *)
Definition list123' := cons 1 (cons 2 (cons 3 nil)).
Definition list222 := repeat 2 3.


(*---Way2---(更通用)*)
Fixpoint repeat2 {X:Type} (x:X) (n:nat):list X :=	(*在定义时就简化*)
  match n with
  | O => nil
  | S n' => cons x (repeat2 x n')
  end.

Definition list333 := repeat2 3 3.

(*事实上第二种方法可以用在任何参数表中*)
(*eg:*)
Inductive list' {X:Type} : Type :=	(*这样定义，就省去了nil'和cons'的冗余参数*)
  | nil' : list'					(*等价于使用了:Arguments nil {X}.和Arguments cons {X} _ _.*)
  | cons' : X -> list' -> list'.



(*下面完成list的其它函数定义*)
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


(*   关于省略类型参数的一些补充    *)
(*
	一旦我们用了上述的两种方法之一省略了类型参数，让Coq自动推导，那么就不能再加上去了，
	再加上去就回报错，如"Check nil nat."就不合法，但这样会导致一些问题，如果上下文信息
	不足，Coq无法推导出类型参数的具体值，
		eg:	Definition mynil := nil.	此时无法推出mynil的具体类型
	此时可以通过下面的方法解决：
	way1:补充一定信息使Coq能够推出：
		Definition mynil:list nat := nil.
	way2:在使用了自动推导的标志前加@让其恢复到不自动推导的状态，然后手动加上类型参数
		Definition mynil := @nil nat.
*)


(*-----Fail命令-----*)
(*
	Fail命令可以让原本执行失败的命令给出失败信息后，继续向下执行，
	但原本能够成功的命令用了Fail反而会无法通过，因为该命令并没有Fail。
	eg:
		Fail Definition mynil := nil.	执行通过并给出fail信息。
		Fail Definition mynil := @nil nat.	执行失败因为原命令没有问题。
*)

(*接下来我们定义一些Notation来简化list的操作*)
Notation "x : y" := (cons x y)
  (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

Notation "x ++ y" := (app x y)
  (at level 60, right associativity).

(*---exercise---*)

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



















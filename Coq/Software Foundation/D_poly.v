(*
	包含：
	1. 使用多态来归纳定义数据类型,eg:list
	2. 多态的数据类型的使用及函数的定义
	3. 利用自动类型推导来化简多态下参数冗长的问题
  4. 多态的pair
  5. 多态的option类型
  6. 高阶函数
  7. filter,map,fold函数的实现
*)

Require Export C_lists.

(*polymorphism 多态*)
(*#####################################################*)
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





(* polymorphic pair *)
(*----------------------------------------------------*)
(* 又成为product*)
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


 Fixpoint unzip {X Y:Type} (l:list (prod X Y)):prod (list X) (list Y) :=
   match l with
   | [] => ([],[])
   | x:xl => ((fst x):fst (unzip xl), (snd x):snd (unzip xl))
   end.



(*多态下的可选类型*)
(*------------------------------------------------------------------*)
(*
	与讨论natlist的head时一样，多态的list的head在list为[]时返回值类型与list
	非空时的情况也不一样，处理nat时我们建立一个natoption类型，同样，这里我们需要一个
	多态的option类型。
*)
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

Definition hd_error {X:Type} (l:list X):option X :=
  match l with
  | [] => none
  | x:xl => some x
  end.





(*高阶函数*)
(*####################################################################*)
(*能够返回函数或以函数为参数的函数称为高阶函数*)
Definition doit3times {X:Type} (f:X -> X) (x:X) :X :=
  f (f (f x)).

Example test_doit3times: 
  doit3times minustwo 9 = 3.

  auto.
Qed.

(*用高阶函数实现一下filter函数*)
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

  auto.
Qed.



(* 匿名函数 *)
(*-----------------------------------------------------*)
(*
  使用高阶函数时，我们会经常遇到一种情况：我们需要某个函数做参数，但
  该函数只在这里用一次，这同样需要在外面定义它，然后把它传给这个高阶函数，
  但这样做不仅麻烦，而且会污染命名空间。这是就可以使用匿名函数，也就是没有
  名称的一次性的函数。
*)

Example test_doit3times2:
  doit3times (fun x => x * x) 2 = 256.

  reflexivity.
Qed.
(* 上面例子中的(fun x => x*x)就是匿名函数。 *)

(*some example*)
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



(*----下面我们再实现一下map函数----*)

Fixpoint map {X Y:Type} (f: X -> Y) (l:list X): list Y :=
  match l with
  | [] => []
  | x:xl => (f x):(map f xl)
  end.

Example test_map1: 
  map (fun x => plus 3 x) [2,0,2] = [5,3,5]. 
Proof. reflexivity. Qed.

Example test_map2: 
  map evenb [1,2,3,4,5] = [false,true,false,true,false].
Proof. reflexivity. Qed.

Example test_map3: 
  map (fun x => [evenb x, evenb (S x)]) [2,3] = [[true,false],[false,true]].
Proof. reflexivity. Qed.

(* 一个难题 *)

Lemma map_distr :
  forall (X Y:Type) (f:X -> Y) (x:X) (l:list X), map f (l ++ [x]) = (map f l) ++ map f [x].

  intros.
  simpl.
  induction l.
    -simpl. auto.
    -simpl.
     rewrite IHl.
     auto.
Qed.

Theorem map_rev : 
  forall (X Y:Type) (f:X -> Y) (l:list X), map f (rev l) = rev (map f l).

  intros.
  induction l.
    -simpl. auto.
    -simpl.
     rewrite map_distr.
     simpl.
     rewrite IHl.
     auto.
Qed.


(*--------fold函数--------*)

Fixpoint fold {X Y:Type} (f:X -> Y -> Y) (l:list X) (e:Y): Y :=
  match l with
  | [] => e
  | x:xl => f x (fold f xl e)
  end.

(*
  fold f [a1,a2,a3,a4] e
  = f a1 (f a2 (f a3 (f a4 e)))
  当XY为同种类型时，e是f的单位元，即 f a e = a.
    eg: f: mult   e:1
        f: app    e:[]
        f: add    e:0
        f: andb   e:true
*)

Example fold_test1: 
  fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_test2: 
  fold andb [true,false,true,true] true = false.
Proof. reflexivity. Qed.

Example fold_test3: 
  fold app [[1,2],[],[3,4,5]] [] = [1,2,3,4,5].
Proof. reflexivity. Qed.


(*-----返回一个函数的高阶函数-----*)

(*Way1: 用匿名函数实现 *)
Definition plusx (x:nat): nat -> nat :=
  fun t:nat => t + x.

(*Way2: 通过只给出部分参数实现 *)
Definition plusx2 (x:nat): nat -> nat := 
  plus x.

Definition plusx3 := plus 5.



(*--- a lot of exercise ---*)


Module Exercise.

(*用fold实现length*)
Definition fold_length {X:Type} (l:list X):nat :=
  fold (fun _ n => n + 1) l 0.          (*匿名函数的模式匹配*)

Lemma fold_length_property :
  forall (X:Type) (l:list X) (x:X), fold_length (x : l) = (fold_length l) + 1.

  intros.
  induction l.
    -simpl. reflexivity.
    -auto.
Qed.

Theorem fold_length_correct : 
  forall (X:Type) (l:list X), fold_length l = length l.

  intros.
  induction l.
    -simpl. reflexivity.
    -simpl. 
     rewrite <- IHl.
     rewrite fold_length_property.
     rewrite IHl.
     rewrite <- plus_n_Sm.
     rewrite <- plus_n_O.
     reflexivity.
Qed.


(*用fold实现map*)
Definition fold_map {X Y:Type} (f:X -> Y) (l:list X):list Y:=
  fold (fun h t => (f h):t) l [].


Theorem fold_map_correct : 
  forall (X Y:Type) (f:X -> Y) (l:list X), 
    fold_map f l = map f l.

  intros.
  induction l.
    -simpl. reflexivity.
    -simpl.
     rewrite <-IHl.
     reflexivity.
Qed.


(*柯里化*)
Definition prod_curry {X Y K:Type} (f:(prod X Y) -> K) (x:X) (y:Y):K := f (x,y).

(*去柯里化*)
Definition prod_uncurry {X Y K:Type} (f:X -> Y -> K) (p:prod X Y):K :=
  f (fst p) (snd p).

Theorem uncurry_curry : 
  forall (X Y K : Type) (f : X -> Y -> K) (x:X) (y:Y), prod_curry (prod_uncurry f ) x y = f x y.

  intros.
  reflexivity.
Qed.


Theorem curry_uncurry : 
  forall (X Y K : Type) (f :prod X Y -> K) (p: prod X Y), prod_uncurry (prod_curry f ) p = f p.

  intros.
  destruct p.
  reflexivity.
Qed.







End Exercise.
























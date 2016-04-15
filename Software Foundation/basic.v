
(*
	包含：
	1.类型的定义与函数的定义
	2.Example的定义与证明
	3.为函数定义中序记号
	4.匹配的用法
	5.module模块
	6.递归函数的定义
	7.简单的证明:
		simpl.
		reflexivity.
		intros.
		rewrite.
		destruct.
*)




(*---------------------------------------------------*)
(*归纳定义一个新的类型*)
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday :day
  | friday : day
  | saturday : day
  | sunday :day.


(*再定义一个函数处理该类型的数据*)
Definition next_day (d:day) :day :=
	match d with
	| monday => tuesday
	| tuesday => wednesday
	| wednesday => thursday
	| thursday => friday
	| friday => saturday
	| saturday => sunday
	| sunday => monday
	end.

(*执行一下该函数*)
Compute(next_day monday).	(*返回了tuesday!!!*)
(*Coq中不能直接调用函数，只能在Compute中调用*)


(*定义我们自己的bool类型*)
Inductive bool : Type :=
  | true : bool
  | false : bool.

(*定义一些bool上的函数*)
Definition negb (b:bool) :bool :=
	match b with
	| true => false
	| false => true
	end.

Definition andb (b1:bool) (b2:bool) :bool :=
	match b1 with
	| true => b2
	| false => false
	end.

Definition orb (b1:bool) (b2:bool) :bool :=
  	match b1 with
  	| false => b2
  	| true => true
  	end.

(*
Example是一个断言，执行到这时进入交互式证明阶段
Example有自己的名字，这样我们在后面可以再用它
*)
Example test_orb1:
  (orb true false) = true.

(*下面是一个交互式证明过程的指令，证明的是上门的Example*)
Proof. 
  simpl. 
  reflexivity. 
Qed.

(*类似的*)
Example test_orb2: 
	(orb false false) = false.

Proof. 
	simpl.
	reflexivity.
Qed.



Example test_orb3:
	(orb true true) = true.

Proof. 
	simpl.
	reflexivity.
Qed.


(*定义的函数都是前序的，下面我们为函数定义我们熟悉的中序记号*)
Infix "&&" := andb.
Infix "||" := orb.

(*使用它们*)
Example test_orb4: 
	(true||false||false) = true.

Proof. 
	simpl.
	reflexivity.
Qed.


(*不仅数据有类型，函数也有类型*)
Check true.		(* true : bool *)
Check andb.		(* andb : bool -> bool -> bool *)





(*module模块*)
(*-------------------------------------------------------*)
(*
	为了使自己定义的类型函数等与标准库或以定义的有重复冲突
	我们可以把一些定义放在模块中，在模块中可以直接使用我们定义的
	东西(类型，函数，等)，模块结束后它们并不会消失，但在模块外不
	能直接使用，必须通过"模块名.xxx"来调用它们。类似于命名空间，
	但不像块，因为块结束后其中定义的东西也都消失了。
*)

Module Playground1.

(*定义自己的nat类型*)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.		(*这才是真正的归纳定义!!! cool!!!*)


(*定义一些nat的函数*)
Definition pred (n:nat) :nat :=
  match n with
  | O => O
  | S n1 => n1			(*n1是n去掉开头的S剩余的部分*)
  end.

End Playground1.
(*到此模块就结束了*)

(*事实上Coq自己的nat就是这样实现的，下面我们为Coq的nat定义一些函数*)

Definition minustwo (n:nat) :nat :=
  match n with
  | O => O
  | S O => O
  | S (S nl) => nl
  end.


(*!!!递归函数!!!*)
(*--------------------------------------------------------*)
(*Coq中的递归函数不用Definition定义而是用Fixpoint定义*)

(*下面我们递归定义一个函数，判断一个自然数是否是偶数*)
Fixpoint evenb (n:nat) :bool :=
  match n with
  | O => true
  | S O => false
  | S (S nl) => evenb nl 
  end.

(*来个小证明*)
Example evenb1:
	(evenb 8) =true.

Proof. 
	simpl.
	reflexivity.
Qed.


(*下面我们定义两个参数的递归函数*)
Fixpoint myplus (n:nat) (m:nat) :nat :=
  match n with
  | O => m
  | S nl => S (myplus nl m)
  end.



(*如果函数的参数中相同的类型可以写在一起，即放在一个括号中*)
(*eg:*)
Fixpoint mymult (n m:nat) :nat:=
  match n with
  | O => O
  | S nl => myplus m (mymult nl m)
  end.

(*再来个证明*)
Example test_mymult:
	(mymult 3 4) = 12.

Proof. 
	simpl.
	reflexivity.
Qed.


(*下面我们尝试匹配更多的参数*)
Fixpoint myminus (n m:nat) :nat :=
  match n, m with
  | O,_ => O
  | S _, O => n
  | S nl, S ml => myminus nl ml
  end.


(*再练习一下*)
Fixpoint myexp (base power:nat) :nat :=
  match power with
  | O => S O
  | S p => mymult base (myexp base p)
  end.


(*Coq还支持嵌套地匹配*)
Fixpoint myequ (n m:nat) :bool :=
  match n with
  | O => match m with
  		 | O => true
  		 | S ml => false
  		 end
  | S nl => match m with
  			| O => false
  			| S ml => myequ nl ml
  			end
  end.

(*但嵌套匹配都能用多参数匹配实现,最好不要用这种麻烦的写法，这只是个例子*)

(*现在我们用单层匹配实现它*)
Fixpoint myequ2 (n m:nat) :bool :=
  match n,m with
  | O,O => true
  | S _,O => false
  | O,S _ => false
  | S nl,S ml => myequ2 nl ml
  end.





(*证明*)
(*------------------------------------------------------*)
(*
	证明由定理(引理，例子...)和证明序列构成
	定理是一个逻辑表达式，证明序列是一些tactics。
	格式

	关键字 its_name:
		logic_expression.

	Proof.
		tactic1.
		tactic2.
		tactic3.
		...
	Qed.

	其中关键字有：Example,Theorem,Lemma,Fact,Remark.
	它们对Coq来说没有任何区别，这些关键字只是为了方便人类分类。

	有时我们知道一个定理是正确的可以在证明里先用:
	Proof.
		Admitted.
	Qed.
	来跳过证明默认它成立，然后来做其他更重要的证明，当后面的证明有意义时再回过头
	给出它完整的证明，如果最后并没有用到它便可以将其删去，这样防止因为失败的尝试而进行不必要的证明。
*)

(*eg:*)

Theorem plus_O_n :
	forall n:nat, (myplus O n) = n.

Proof. 
	intros n.
	reflexivity.
Qed.
(*
	下面介绍一些基本的tactic：
	1.simpl			化简，能够将目标进行化简以方便阅读
	2.reflexivity	证明两侧相等，很强大，能够自动化简，展开等
	3.intros n:nat 	上面我们用了forall n，因此要证明对任意的n后面的
					都成立，intros n表示引入任意一个n。
*)
(*
	当我们在证明中卡住的时候可以输入 "Abort." 来终止当前证明。
*)




(*-------proof by rewrite*)
(*一个复杂的例子*)
Theorem plus_id_example :
	forall n m:nat, n = m -> n + n = m + m.


Proof. 
	intros n m.		(*将n,m作为假设引入*)
	intros H.		(*将 n = m 作为假设引入，并命名为H*)
	rewrite -> H.	(*根据假设H重写目标，－> 表示将n替换为m，同理 <- 表示将m替换为n*)
	reflexivity.	
Qed.


(*再来一个*)
Theorem plus_id_exercise : 
	forall n m l:nat, n = m -> m = l -> n + m = m + l.

Proof.
	intros n m l.
	intros H1.
	intros H2.
	rewrite H1.
	rewrite H2.
	reflexivity.
Qed.


(*------------proof by case analysis*)

Theorem myequ_test :
	forall n:nat, (myequ (n+1) 0) =false.
(*
	这里myequ对n+1的处理要分情况进行(因为函数定义中使用了match)，前面的例子中
	没有出现类似的情况，这种情况下的证明要使用新的tactic: destruct。
*)

Proof. 
	intros n.
	destruct n as [ |n'].	(*将n按照nat的定义分为两种情况，as后面的[]为每种
							情况产生的变量命名，as可以不写Coq会自动为其命名，但不推荐这样*)
		-reflexivity.		(*前面的 "-" 叫bullet,有多个subgoal时可以按subgoal分别证明
							若不写"-",则将所有的subgoal串起来一起证，比较乱，最好写上*)
		-reflexivity.
Qed.


(*yet another*)
Theorem myminus_test : 
	forall n:nat, (myminus n O) = n.

Proof. 
	intros n.
	destruct n.
		-reflexivity.
		-reflexivity.
Qed.



(*在分情况的subgoal中继续分情况*)
Theorem myand_commu : 
	forall a b:bool, (andb b a) = (andb a b).

Proof. 
	intros a b.
	destruct a.
		-destruct b.		(*在subgoal中继续destruct*)
			+reflexivity.	(*在不同的层中使用不同的bullet*)
			+reflexivity.
		-destruct b.
			+reflexivity.
			+reflexivity.
Qed.

(*Coq支持3种不同的bullet: -,+,*)
(*但对于有很多层的subgoal可以使用{}来分离每一个subgoal的证明*)
(*
eg:

Proof. 
	intros a b.
	destruct a.
		{destruct b.
			{reflexivity.}
			{reflexivity.}}
		{destruct b.
			{reflexivity.}
			{reflexivity.}}
Qed.
*)

(*也可以把{}与-,+,*混合着用，这样会更方便*)
(*eg:

Proof. 
	intros a b.
	destruct a.
		{destruct b.
			-reflexivity.
			-reflexivity.}
		{destruct b.
			-reflexivity.
			-reflexivity.}
Qed.
*)




(*-------------------------exercise----------------------*)
Theorem andb_true_elim2 : 
	forall b c:bool, (andb b c) = true -> c = true.

Proof.
  intros b c.
  intros H1.
  rewrite <- H1.
  destruct b.
    -simpl.
     reflexivity.
    -simpl.
     destruct c.
        +rewrite <- H1.
         reflexivity.
        +reflexivity.
Qed.


(*Coq甚至能够证明高阶逻辑*)
Theorem high_order_logic : 
	forall f:bool -> bool, (forall x:bool, f x = x) -> forall b:bool, f (f b) = b.

Proof.
  intros f.
  intros H1.
  intros b.
  destruct b.
    -rewrite H1.
     rewrite H1.
     reflexivity.
    -rewrite H1.
     rewrite H1.
     reflexivity.
Qed.


Theorem andb_equ_orb :
	forall b c:bool, (andb b c = orb b c) -> b = c.

Proof.
  intros b c.
  destruct b.
    -simpl.
     intros H1.
     rewrite H1.
     reflexivity.
    -simpl.
     intros H2.
     rewrite H2.
     reflexivity.
Qed.













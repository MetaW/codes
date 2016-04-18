(*
	CONTENT	:
	1.	apply
	2.	symmetry
	3.	apply...with...
	4.	inversion
	5.
*)

Require Export poly.
Require Export lists.




(* tactic: apply *)
(*-------------------------------------------------------------------------*)
(*look a example*)


Theorem silly1 : 
	forall (n o m p:nat), n = m -> [n,o] = [n,p] -> [n,o] = [m,p].
  intros n o m p eq1 eq2.
  rewrite <- eq1.
  apply eq2.	(*here we use "apply eq2" to replace "rewrite eq2. reflexivity."*)
Qed.


(*another example*)
Theorem silly2 : 
	forall (n o m p:nat), n = m -> (forall (q r:nat), q =r -> [q,o] = [r,p] ) -> [n,o] = [m,p].

  intros n m o p eq1 eq2.
  apply eq2.	(*with hypotheses A->B and goal B, apply A->B to goal B can transfer goal to A*)
  apply eq1.	(*with hypotheses A and goal A apply A can finish the proof*)
Qed.

Theorem silly2a : 
	forall (n m:nat), (n,n) = (m,m) -> (forall (q r:nat), (q,q) = (r,r) -> [q] = [r] ) -> [n] = [m].

  intros.
  apply H0.
  apply H.
Qed.

Fixpoint oddb (n:nat):bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => oddb n'
  end.

Theorem silly_ex : 
	(forall n, evenb n = true -> oddb (S n) = true ) -> evenb 3 = true -> oddb 4 = true.

  intros.
  apply H.
  apply H0.
Qed.

(*
	the knowen fact being applied must match the goal exactly. 
	for example, apply will not work if the left and right 
	sides of the equality are swapped. 
	
	And applycan be used not only with hypo but proved theorem.
	
	ps: apply a fact with "forall" Coq can auto match the goal if
		it can really match like the rewrite.
*)

Fixpoint beq_nat (n m:nat):bool :=
  match n,m with
  | O,O => true
  | O,_ => false
  | _,O => false
  |S n',S m' => beq_nat n' m'
  end.

Theorem silly3 : 
	forall n:nat, true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.

  intros.
  simpl.
  rewrite H.	(*we can not use apply here for equality are swapped in the goal*)
  reflexivity.
Qed.

(*but the "symmetry" tactic can swap the left and the right side of the equality in the goal*)
Theorem silly3a : 
	forall n:nat, true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.

  intros.
  simpl.
  symmetry.
  apply H.
Qed.


Theorem rev_exer : 
	forall (n m:list nat), n = rev m -> m = rev n.

  intros.
  rewrite H.
  symmetry.
  apply  rev_involutive.
Qed.



(*  apply ... with ...*)
(*------------------------------------------------------------*)
(*
	用rewrite来使用已经证明过的结论时比较局限，有时会遇到已知定理与目标
	无法匹配的情况，此时apply就发挥了作用，apply比rewrite功能要强，可以
	直接利用更加复杂的定理来匹配目标，如果apply不知道如何匹配就回发出错误警告，
	提示无法为某个变量找到匹配的东西，这时应该用with来告诉它应该匹配什么。
*)

(*下面是等价关系的传递率，rewrite很难利用这种复杂的结论*)
Lemma trans_eq : 
	forall (X:Type) (n m o:X), n = m -> m = o -> n = o.

	intros X n m o eq1 eq2.
	rewrite <- eq2.
	apply eq1.
Qed.

(*example 1*)
Example trans_eq_example: 
	forall (a b c d e f:nat), [a,b] = [c,d] -> [c,d] = [e,f] -> [a,b] = [e,f].

  intros.
  apply trans_eq with [c,d].(*没有with时会警告m无法找到匹配的东西，此时我们告诉它用[c,d]匹配*)
  apply H.
  apply H0.
Qed.

(*example 2*)
Example trans_eq_exercise: 
	forall (n m o p:nat), m = (minustwo o) -> (n+p) = m -> (n+p) = (minustwo o).

  intros.
  apply trans_eq with m.(*同上一个例子*)
  apply H0.
  apply H.
Qed.





(* inversion *)
(*#####################################################################*)
(*
	由于归纳定义类型时，不同的constructer默认就具有两个性质：
	1.injective (单射／一一映射)	eg: S n = S m -> n = m
	2.disjoint	(不相交)			eg: true != false , O != S n (对任意的n) 
	  即不同的constructer之间不产生相同的实例。

	inversion是用来处理hypotheses的tactic，如果hypotheses的形式为
		H：c a1 a2 ... an = d b1 b2 ... bm (其中c,d为constructer)
	1.那么如果c,d为相同的constructer那么由单射性可知：a1 = b1, a2 = b2, ...
	inversion将这些facts加入到hypo中，并自动用他们rewrite目标。
	2.如果c,d是不同的consturctern那么H就是有矛盾的，即错误的，那么inversion就
	  将当前的goal pass掉，直接进入下一个goal或结束证明。
*)

Theorem S_injective : 
	forall (n m:nat), S n = S m -> n = m.

  intros.
  inversion H.
  reflexivity.
Qed.


Theorem inversion_ex1 : 
	forall (n m o:nat), [n,m] = [o,o] -> [n] = [m].

  intros.
  inversion H.
  reflexivity.
Qed.

(*与induction类似，inversion也可以自己定义新产生的hypo的名字，用"as [..]"*)
Theorem inversion_ex2 : 
	forall (n m:nat), [n] = [m] -> n = m.

  intros.
  inversion H as [W].
  reflexivity.
Qed.

Theorem inversion_ex3 : 
	forall (X:Type) (x y z:X) (l j:list X), x:y:l = z:j -> y:l = x:j -> x = y.

  intros.
  inversion H0.
  reflexivity.
Qed.



(*下面两个例子说明“错误的前提可以得到任何结论”的规则也能用inversion实现*)
(*这条规则又叫做：principle of explosion*)
Theorem inversion_ex4 : 
	true = false -> 1 + 1 = 3.

  intros.
  inversion H.	(*H是错误的前提*)
Qed.

Theorem inversion_ex5 : 
	forall n:nat, S n = O -> 1 + 1 = 12345.

  intros.
  inversion H.	(*H是错误的前提*)
Qed.


Example inversion_ex6: 
	forall (X:Type) (x y z:X) (l j:list X), x:y:l = [] -> y:l = z:j -> x=z.

  intros.
  inversion H.
Qed.






























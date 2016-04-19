(*
	CONTENT	:
	1.	apply
	2.	symmetry
	3.	apply...with...
	4.	inversion
	5.  对hypo进行操作
  6.  前向推理与后向推理
  7.  
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






(* using tactics on hypotheses *)
(*---------------------------------------------------------------*)
(*
  之前的大多数tactic都只讲了如何对goal进行操作，事实上它们也能对hypo进行操作，
  只需要在tactic后面加上"in H"就行了，eg:
    simpl in H.
    apply L in H1.
    symmetry in H
    ...
  induction由于同时作用于hypo与goal所以没必要加"in hypo"，另外inversion本身就是对
  hypo进行操作的tactic所以也不用加"in hypo".

  其中apply L in H比较重要，对goal进行处理时，如apply L，若L为A -> B的形式，
  goal为B那么执行之后goal变为A. 这种证明方法称为后向推理(backword reasoning)；
  当apply处理H时，仍令L为A -> B的形式，这是H一般要为A，执行之后将H转化为B，
  这种证明方式称为前向推理(forward reasoning).
  前向推理一般从hypo出发一步步得到goal，而后向推理则从goal出发向后寻找goal成立的条件
  直到条件为已知的hypo为止。
  
  在Coq中一般后向推理用的比较多。
*)
(* exercise *)

Theorem S_inj : 
  forall (n m:nat) (b :bool), beq_nat (S n) (S m) = b -> beq_nat n m = b.

  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly_ex1 : 
  forall n:nat, (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) -> true = beq_nat n 5 -> true = beq_nat (S (S n)) 7.

  intros.
  symmetry in H0.
  apply H in H0.
  symmetry.
  apply H0.
Qed.





(*
  //TODO
  -some thing about intros and induction
  -generalize dependent
*)

Theorem plus_n_n_injective : 
  forall (n m:nat), n+n = m+m -> n = m.

  intros n.
  induction n as [| n'].
   -intros m eq.
    induction m as [| m'].
     +reflexivity.
     +inversion eq.
   -intros m eq.
    induction m as [| m].
     +inversion eq.
     +apply f_equal.
      rewrite <- plus_n_Sm in eq.
      simpl in eq.
      rewrite <- plus_n_Sm in eq.
      inversion eq.
      apply IHn' in H0.
      apply H0.
Qed.



Theorem double_injective : 
  forall (n m:nat), double n = double m -> n = m.

  intros n.
  induction n as [| n'].
    -simpl. intros m eq. 
     induction m as [|m'].
      +reflexivity.
      +inversion eq.
    -simpl.
     intros m eq.
     induction m as [|m'].
      +simpl in eq.  inversion eq.
      +apply f_equal.
       apply IHn'.
       simpl in eq.
       inversion eq.
       reflexivity.
Qed.


Theorem beq_nat_true:
  forall (n m:nat), beq_nat n m = true -> n = m.
  
  intros n.
  induction n as [|n'].
    -simpl. intros m eq.
     induction m as [|m'].
      +reflexivity.
      +inversion eq.
    -simpl. intros m eq.
     induction m as [|m'].
      +inversion eq.
      +apply IHn' in eq.
       apply f_equal.
       apply eq.
Qed.


Theorem double_injective2 : 
  forall (n m:nat), double n = double m -> n = m.

  intros n m.
  generalize dependent n.
  induction m as [|m'].
    -simpl. intros n eq.
     induction n as [|n'].
      +reflexivity.
      +simpl in eq. inversion eq.
    -simpl. intros n eq.
     induction n as [|n'].
      +inversion eq.
      +simpl in eq.
       inversion eq.
       apply IHm' in H0.
       apply f_equal.
       apply H0.
Qed.


Theorem beq_id_true : 
  forall x y, beq_id x y = true -> x = y.

  intros x.
  induction x.
  intros y.
  induction y.
  intros eq.
  apply beq_nat_true in eq.
  apply f_equal.
  apply eq.
Qed.



(* some exercise *)
Theorem nth_error_after_last:
  forall (n:nat) (X:Type) (l:list X), length l = n -> nth_error l n = none.

  intros n X.
  induction n.
    -intros l eq.
     induction l.
      +simpl. reflexivity.
      +simpl. inversion eq.
    -intros l eq.
     induction l.
      +simpl. reflexivity.
      +simpl. simpl in eq.
       inversion eq.
       rewrite H0.
       apply IHn in H0.
       apply H0.
Qed.


Theorem app_length_cons : 
  forall (X:Type) (l1 l2:list X) (x:X) (n:nat), length (l1 ++ (x:l2)) = n -> S (length (l1 ++ l2)) = n.

  intros X l1.
  induction l1.
    -intros l2 x n.
      +simpl. intros eq. apply eq.
    -intros l2 x0 n eq.
     simpl. simpl in eq.
     induction n.
      +inversion eq.
      +inversion eq.
       rewrite H0.
       apply IHl1 in H0.
       apply f_equal.
       apply H0.
Qed.

Theorem app_length_twice : 
  forall (X:Type) (n:nat) (l:list X), length l = n -> length (l ++ l) = n + n.

  intros X n.
  induction n.
    -intros l eq.
     induction l.
      +simpl. reflexivity.
      +simpl in eq. inversion eq.
    -intros l eq.
     induction l.
      +simpl in eq. inversion eq.
      +simpl in eq. inversion eq.
       simpl. apply f_equal.
       rewrite H0.
       rewrite app_length.
       simpl. rewrite H0.
       reflexivity.
Qed.

Theorem double_induction : 
  forall (P:nat -> nat -> Prop), P O O -> (forall (m:nat), P m O -> P (S m) O)
    -> (forall n:nat, P O n -> P O (S n)) -> (forall (m n:nat), P m n -> P (S m) (S n)) -> forall (m n:nat), P m n.

  intros P.
  intros P0.
  intros H1.
  intros H2.
  intros H3.
  intros m.
  induction m.
    -intros n.
     induction n.
      +apply P0.
      +apply H2 in IHn.
       apply IHn.
    -intros n.
     induction n.
      +apply H1 in IHm. apply IHm.
      +apply H3.
       apply IHm.
Qed.
   







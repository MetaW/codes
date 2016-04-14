
(*
	包含：
	1.
	2.
	3.

*)

(*######################################################*)
Require Export induction.

Module NatList.	(*为避免冲突我们将其放在一个m模块中*)

(*定义nat的pair类型*)
(*------------------------------------------------------*)
Inductive natprod : Type :=
  | pair: nat -> nat -> natprod.

(*再定义几个函数*)
Definition fst (n:natprod) :nat :=
	match n with
	| pair x y => x
	end.

Definition snd (n:natprod) :nat :=
  match n with
  | pair x y => y
  end.

(*每次写pair x y太麻烦，可以定义一个标记*)
Notation "( x , y )" := ( pair x y ).

(*再为新的标记定义几个函数*)
Definition fst' (n:natprod):nat :=
  match n with
  | (x,y) => x
  end.

Definition snd' (n:natprod):nat :=
  match n with
  | (x,y) => y 
  end.

Definition swap_pair (p:natprod):natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(*a proof*)
Theorem surjective_pairing_stuck : 
	forall p:natprod, p = (fst p, snd p).

	intros p.
	destruct p.
	simpl.
	reflexivity.
Qed.	


Theorem snd_fst_is_swap : 
	forall p:natprod, (snd p, fst p) = swap_pair p.
	
	intros p.
	destruct p.
	simpl.
	reflexivity.
Qed.	



(*定义nat的list类型*)
(*------------------------------------------------------*)
Inductive natlist : Type :=
  | nil :natlist
  | cons :nat -> natlist -> natlist.


(*eg*)
Definition mylist :natlist := cons 1 (cons 5 (cons 3 nil)).


(*为了使用方便，再定义几个notation*)
Notation "x : l" := (cons x l)
	(at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil)..).
(*上面的notation定义不理解也没关系
但要注意notation前一部分""中不同成
分之间必须用空格分开，连在一起会出现错误*)

(*这样下面几个定义就是等价的了*)
Definition mylist1 :natlist := 1:2:3:[].
Definition mylist2 :natlist := 1:(2:(3:nil)).
Definition mylist3 :natlist := [1,2,3].



(*为natlist定义一些函数*)
Fixpoint repeat (n count:nat) :natlist :=
  match count with
  | O => []
  | S count' => n:(repeat n count')
  end.

Fixpoint length (l:natlist) :nat:=
  match l with
  | nil => O
  | cons x l' => S (length l')
  end.

Fixpoint app (l1 l2:natlist) :natlist :=
  match l1 with
  | nil => l2
  | cons x l1' => cons x (app l1' l2)
  end.

(*app用的多，再给他定义一个符号吧*)
Notation "x ++ y" := (app x y)
	(at level 60, right associativity).



(*-----------a lot of exercise!!!----------------*)
Example test_app1: 
  [1,2,3] ++ [4,5] = [1,2,3,4,5].

  simpl.
  reflexivity.
Qed.

(*head tail*)
Definition hd (defou :nat) (p:natlist):nat :=
  match p with
  | [] => defou
  | x:xl => x
  end.

Definition tl (p:natlist):natlist :=
  match p with
  | nil => nil
  | x:xl => xl
  end.

(*more function*)
Fixpoint noneZero (p:natlist):natlist :=
  match p with
  | [] => []
  | O:xl => noneZero xl
  | x:xl => x:(noneZero xl)
  end.

Example test_noneZero: 
  noneZero [0,1,2,0,0,3,0] = [1,2,3].

  simpl.
  reflexivity.
Qed.


Fixpoint odd (n:nat):bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => odd n'
  end.

Fixpoint oddnumbers (p:natlist):natlist :=
  match p with
  | [] => []
  | x:xl => match odd x with
            | true => x:(oddnumbers xl)
            | false => oddnumbers xl
            end
  end.

Example test_oddnumbers: 
  oddnumbers [0,1,2,0,3,4,5,6] = [1,3,5].
  
  simpl.
  reflexivity.
Qed.



Fixpoint countoddmembers (p:natlist):nat :=
  match p with
  | [] => O
  | x:xl => match odd x with    (*双层的match!!!*)
            | true => 1+(countoddmembers xl)
            | false => countoddmembers xl
            end
  end.

Example test_countoddmembers: 
  countoddmembers [0,1,2,3,4,5,0,6] = 3.

  simpl.
  reflexivity.
Qed.

Example test_countoddmembers2: 
  countoddmembers [0,2,4,6,8] = 0.

  simpl.
  reflexivity.
Qed.

Example test_countoddmembers3: 
  countoddmembers nil = 0.

  simpl.
  reflexivity.
Qed.

Fixpoint alternate (l1 l2:natlist):natlist :=
  match l1,l2 with
  | nil,_ => l2
  | _,nil => l1
  | x:xl,y:yl => x:y:(alternate xl yl) 
  end.

Example test_alternate1: 
  alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].

  simpl.
  reflexivity.
Qed.


Example test_alternate2: 
  alternate [1] [2,3,4] = [1,2,3,4].

  simpl.
  reflexivity.
Qed.


Example test_alternate3: 
  alternate [1,2,3] [4] = [1,4,2,3].

  simpl.
  reflexivity.
Qed.


Example test_alternate4: 
  alternate [] [1,2,3] = [1,2,3].

  simpl.
  reflexivity.
Qed.


(*------------下面定义一种多重集合bag，他与natlist是同一种东西*)
Definition bag := natlist.


(*定义一些函数*)

Fixpoint eq (n m:nat) :bool:=
  match n,m with
  | O,O => true
  | O,S x => false
  | S x,O => false
  | S n', S m' => eq n' m'
  end.

Fixpoint count (v:nat) (b:bag) :nat :=
  match b with
  | [] => O
  | x:xl => match (eq x v) with
            | true => 1 + (count v xl)
            | false => count v xl
            end
end.


Example test_count1: 
  count 1 [1,2,3,2,1,0,1] = 3.

  simpl.
  reflexivity.
Qed.


Example test_count2: 
  count 6 [1,2,3,4,5] = 0.

  simpl.
  reflexivity.
Qed.

Definition sum_bag (b1 b2:bag):bag :=
  b1 ++ b2.

Example test_sum1: 
  count 1 (sum_bag [1,2,1] [3,4,1]) = 3.
  
  simpl.
  reflexivity.
Qed.

Definition add (v:nat) (b:bag) :bag :=
  v:b.

Example test_add1: 
  count 1 (add 1 [1,2,3,4,1]) = 3.

  simpl. reflexivity.
Qed.

Example test_add2: 
  count 5 (add 1 [1,2,3,1,3]) = 0.

  simpl. reflexivity.
Qed.

Definition member (v:nat) (b:bag):bool :=
  match (count v b)  with
  | O => false
  | S _ => true
  end.

Example test_member1: 
  member 1 [1,2,3,4] = true.

  reflexivity.
Qed.


Example test_member2: 
  member 5 [1,2,3,4] = false.

  reflexivity.
Qed.


///// to page 61.

End NatList.




























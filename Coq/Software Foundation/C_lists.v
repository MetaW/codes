
(*
	包含：
	1.	pair 的定义及相关函数的实现
	2.	natlist的定义及相关函数与证明
	3.	非常有用的命令 SearchAbout xxx. 能够查找出目前已经证明过
		的名字中包含xxx的定理，在证明时查找已经证明过的定理时很有用.
 	4.  type定义补充!!!.
 	5.  Coq中的if-else
 	6.  map的定义及相关函数和证明
*)

(*######################################################*)
Require Export B_induction.

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
(*####################################################################*)
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


(*------------下面定义一种多重集合bag，他与natlist是同一种东西---*)
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



(*  Reasoning about list  *)
(*####################################################################*)
Theorem nil_app : 
	forall l:natlist, [] ++ l = l.

  reflexivity.
Qed.


Theorem tl_length_pred : 
	forall l:natlist, pred (length l) = length (tl l).

  intros l.
  destruct l.
    -simpl.
     reflexivity.
    -simpl.
     reflexivity.
Qed.


Theorem app_assoc:
	forall l1 l2 l3:natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  
  intros l1 l2 l3.
  induction l1.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHl1.
     reflexivity.
Qed.

(*定义反转list的函数*)

Fixpoint rev (l:natlist): natlist :=
  match l with
  | nil => nil
  | x:l' => (rev l') ++ [x]
  end.

Example test_rev1: 
	rev [1,2,3] = [3,2,1].

  simpl.
  reflexivity.
Qed.

Example test_rev2: 
	rev nil =nil.

  simpl.
  reflexivity.
  Qed.


Theorem app_length : 
	forall l1 l2:natlist, length (l1 ++ l2) = (length l1) + (length l2).

  intros l1 l2.
  induction l1.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHl1.
     reflexivity.
Qed.




Theorem rev_length :
	forall l:natlist, length (rev l) = length l.

  intros l.
  induction l.
    -simpl.
     reflexivity.
    -simpl.
     rewrite app_length.
     rewrite IHl.
     simpl.
     rewrite plus_commu.	(*plus_commu来自induction.v,由于前面引入了*)
     simpl.					(*所以在这里可以直接使用！！！*)
     reflexivity.
Qed.


(*
	SearchAbout xxx. 能够查询的东西仅包括证明，不能查询函数等东西，
	它能查所有类型的证明，包含Example,Theorem,Lemma等。
	eg:
	SearchAbout rev.
	可以得到：
		test_rev1
		test_rev2
		rev_length
	及对应的具体内容。
*)


(*----------- a lot of exercise ---------*)

Theorem app_nil_r : 
	forall l:natlist, l ++ [] = l.

  intros l.
  induction l.
    -simpl.
     reflexivity.
    -simpl.
     rewrite -> IHl.
     reflexivity.
Qed.

Theorem rev_tail_app :
  forall (l:natlist) (n:nat), rev (l ++ [n]) = n:rev l.

  intros l n.
  induction l.
    -simpl.
     reflexivity.
    -simpl.
     rewrite IHl.
     simpl.
     reflexivity.
Qed.

Theorem rev_involutive : 
  forall l:natlist, rev (rev l) = l.

  intros l.
  induction l.
    -simpl.
     reflexivity.
    -simpl.
     assert(H: n:rev (rev l) = n:l).
      { rewrite IHl. reflexivity. }
     rewrite <- H.
     rewrite rev_tail_app.
     reflexivity.
Qed.

Theorem app_assoc4 : 
  forall l1 l2 l3 l4:natlist, 
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.

  intros l1 l2 l3 l4.
  assert(H: ((l1 ++ l2) ++ l3) ++ l4 = (l1 ++ l2) ++ (l3 ++ l4)).
    { rewrite app_assoc. reflexivity. }
  rewrite H.
  rewrite app_assoc.
  auto.
Qed.

Theorem noneZero_app : 
  forall l1 l2:natlist, noneZero (l1 ++ l2) = (noneZero l1) ++ (noneZero l2).

  intros l1 l2.
  induction l1.
    -simpl.
     auto.
    -simpl.
     induction n.
      +rewrite IHl1.
       auto.
      +simpl.
       rewrite IHl1.
       auto.
Qed.



Fixpoint beq_natlist (l1 l2:natlist) :bool :=
  match l1,l2 with
  | [],[] => true
  | [],_:_ => false
  | _:_,[] => false
  | x:xl,y:yl => match (eq x y) with
                | true => beq_natlist xl yl
                | false => false
                end
  end.


Theorem beq_natlist_refl : 
  forall l:natlist, true = beq_natlist l l.

  intros l.
  induction l.
    -simpl.
     auto.
    -simpl.
     induction n.
      +simpl.
       rewrite IHl.
       auto.
      +simpl.
       rewrite IHn.
       reflexivity.
Qed.

Theorem rev_injective : 
  forall l1 l2:natlist, rev l1 = rev l2 -> l1 = l2.

  Admitted.
(*这个证明需要用到false -> anything,目前不会这个tactic*)







(*---------type定义补充----------*)
(*####################################################*)
(*
  type的定义我们一般用Inductive做归纳定义，得到一个递归集作为一个
  type，然而有时我们需要在一个type中再添加一些不属于这个集合的元素
  这就需要新定义一个类型，这个类型将这个type和这外来些元素并在一起。
  方法为：
*)
(*
  eg: 如果我们的函数在一般情况下返回nat,但在某些情况下返回别的类型，这
      种情况是无法实现的，除非新定义一个类型包含他们。
      再定义一个函数将新类型转化为nat，如果不能转的话就返回默认值(虽然这种做法很不好)。
*)

Inductive natoption : Type :=
  | some : nat -> natoption   (*!!!不能用 "x:nat" 这样直接将nat类型并入*)
  | none : natoption.          (*因为Inductive要求所有情况的类型必须与定义的一致*)

(*这样就可以定义下面这个函数了，它根据下标返回natlist的对应值*)


Fixpoint nth_error (n:nat) (l:natlist) :natoption :=
  match n,l with
  | _, nil => none
  | O, x:xl => some x
  | S n', x:xl => nth_error n' xl
  end.


Definition option_elim (default:nat) (op:natoption):nat :=
  match op with
  | none => default
  | some x => x 
  end.






(* if-else *)
(*####################################################*)
(*
  Coq中的if-else语法上与Haskell一样,但由于Coq的bool并不其他语言
  中用的那么多，所以Coq的if-else不止能判断bool类型，还能判断其他类型,
  事实上，他能判断任何仅有两个归纳项定义的类型，如果条件与第一个匹配就执行
  if后面的语句，如果与第二个匹配就执行else后面的语句。

  事实上if-else不是必须的，用match完全可以代替它。
*)
(*eg: *)

Fixpoint nth_error2 (n:nat) (l:natlist) :natoption :=
  match l with
  | nil => none
  | x:xl => if (eq n O) then some x else nth_error2 (n-1) xl
  end.


End NatList.







(*------map-------*)
(*####################################################*)
(*
  我们在这一部分定义一个map，但用的是类似于list的结构，因为它可以有重复，
  所以是个multimap，这里map由于是线性结构的所以操作效率较低，只是作为例子。
*)

(*先定义id作为key的类型*)
Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2:id):bool :=
  match x1,x2 with
  | Id x,Id y => NatList.eq x y
  end.



(*开始定义map了*)
Module MyMap.
Import NatList.

Inductive my_map : Type :=
  | empty : my_map
  | record : id -> nat -> my_map -> my_map.

(*定义插入函数*)

Definition insert (key:id) (val:nat) (m:my_map):my_map :=
  record key val m.

Fixpoint find (key:id) (m:my_map):natoption :=
  match m with
  | empty => none
  | record k v m' => if beq_id key k then some v else find key m'
  end.

Theorem insert_eq : 
  forall (m:my_map) (k:id) (v:nat), find k (insert k v m) = some v.

  intros m k v.
  simpl.
  assert(H: beq_id k k = true).
    { induction k. simpl. 
      induction n.
        -simpl. auto.
        -simpl. rewrite IHn. auto.
    }
  rewrite H.
  reflexivity.
Qed.

Theorem insert_neg : 
  forall (m:my_map) (x y :id) (v:nat), (beq_id x y = false) -> (find x (insert y v m)) = find x m.

  intros m x y v.
  simpl.
  intros H.
  rewrite H.
  reflexivity.
Qed.

End MyMap.




















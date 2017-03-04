(*
  contents:
  1. 如何定义可能不停机的函数
  2. step_indexed求值函数与关系的等价性证明!!!
  3.
*)

Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import L_imp.
Require Import H_maps.




(* 如何定义可能不停机的函数 *)
(*
imp的解释器求值方程ceval，因为解释WHILE语句可能进入死循环，因此ceval可能
不停机，Coq不允许定义此类函数，因此会抛出错误：Cannot guess decreasing 
argument of fix。解决办法是：给ceval函数加一个参数最大递归调用次数，超过
这个次数ceval就立即停机。这样ceval一定能停机也就能够通过Coq了。但这样ceval
的语义与imp的实际语义不完全相同。
*)


(*first try*)
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          t_update st l (aeval st a1)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(*
but we can't tell, from its result, whether it stopped 
because the program terminated normally or because it 
ran out of steps.
so we will return option state instead of state:
*)


Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
match i with
| O => None
| S i' => match c with
          | SKIP => Some st
          | l ::= a1 => let n := (aeval st a1) in
                        Some (t_update st l n)
          | c1 ;; c2 => match (ceval_step3 st c1 i') with
                        | None => None
                        | Some st' => (ceval_step3 st' c2 i')
                        end
          | IFB b THEN c1 ELSE c2 FI => 
              if (beval st b) 
              then ceval_step3 st c1 i'
              else ceval_step3 st c2 i'
          | WHILE b1 DO c1 END =>
              if (beval st b1)
              then match (ceval_step3 st c1 i') with 
                  | None => None
                  | Some st' => ceval_step3 st' c i'
                  end
              else Some st
          end
end.


(*
为了减少match使用时的繁琐，定义下面的语法糖：
*)
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) :option state :=
match i with
| O => None
| S i' => match c with
          | SKIP => Some st
          | l ::= a1 => let n := (aeval st a1) in
                        Some (t_update st l n)
          | c1 ;; c2 => LETOPT st' <== (ceval_step st c1 i') IN
                        ceval_step st' c2 i'
          | IFB b THEN c1 ELSE c2 FI => 
              if (beval st b) 
              then ceval_step st c1 i'
              else ceval_step st c2 i'
          | WHILE b1 DO c1 END =>
              if (beval st b1)
              then LETOPT st' <== (ceval_step st c1 i') IN
                   (ceval_step st' c i')
              else Some st
          end
end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.
  
Compute(test_ceval empty_state
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3
            ELSE Z ::= ANum 4
          FI)).



(* exercise *)

Definition pup_to_n : com :=
X ::= (ANum 5);;
Y ::= (ANum 0);;
WHILE BNot (BEq (AId X) (ANum 0)) DO
  Y ::= APlus (AId Y) (AId X);;
  X ::= AMinus (AId X) (ANum 1)
END.

Example pup_to_n_1 :
  test_ceval empty_state pup_to_n = Some (0, 15, 0).
Proof.
  reflexivity.
Qed.







(*step_indexed求值函数与关系的等价性证明!!!*)

Theorem ceval_step__cevalR : forall c st st', (exists i, 
                            ceval_step st c i = Some st') -> c / st \\ st'.
Proof.
  intros c st st' H.
  destruct H as [i E].
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  -intros c st st' H. inversion H.
  -intros c st st' H.
   destruct c;
   simpl in H; inversion H; subst; clear H.
   +apply E_Skip.
   +apply E_Ass. auto.
   +destruct (ceval_step st c1 i') eqn:Heqr1.
    *apply E_Seq with s.
      **apply IHi'. apply Heqr1.
      **apply IHi'. apply H1.
    *inversion H1.
   +destruct (beval st b) eqn:Heqrl.
    *apply E_IfTrue.
      **apply Heqrl.
      **apply IHi'. apply H1.
    *apply E_IfFalse.
      **apply Heqrl.
      **apply IHi'. apply H1.
   +destruct (beval st b) eqn:Heqrl.
    *destruct (ceval_step st c i') eqn:Heqrl'.
      **apply E_WhileLoop with s.
        ***apply Heqrl. ***apply IHi'. apply Heqrl'.
        ***apply IHi'. apply H1.
      **inversion H1.
    *inversion H1. clear H1. apply E_WhileEnd. subst.
     apply Heqrl.
Qed.





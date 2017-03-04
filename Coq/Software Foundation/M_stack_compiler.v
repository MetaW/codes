
Require Import H_maps.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import PeanoNat.
Import ListNotations.

Definition state := total_map nat.  (* define state type *)
Definition empty_state := t_empty 0.


Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".


(* AST *)
Inductive aexp : Type :=
| ANum : nat -> aexp
| AId  : id -> aexp
| APlus   : aexp -> aexp -> aexp
| AMult   : aexp -> aexp -> aexp
| AMinus  : aexp -> aexp -> aexp.



(* Instruction *)
Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.



(* compile *)
Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
| ANum n => [SPush n]
| AId i => [SLoad i]
| APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
| AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
| AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
end.

(* test *)
Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  simpl. auto.
Qed.





(* eval instruction *)
Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr) : list nat :=
match prog with
| [] => stack
| inst :: ll => let sk' := match inst with
                           | SPush n => n::stack
                           | SLoad i => (st i)::stack
                           | SPlus => match stack with
                                      | x1::x2::xl => (x1 + x2)::xl
                                      | _ => []
                                      end
                           | SMinus => match stack with
                                       | x1::x2::xl => (x2 - x1)::xl
                                       | _ => []
                                       end
                           | SMult => match stack with
                                      | x1::x2::xl => (x1 * x2)::xl
                                      | _ => []
                                      end
                           end
                in (s_execute st sk' ll)
end.

(*test*)
Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof.
  simpl. auto.
Qed.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof.
  simpl. auto.
Qed.










(* proof the correctness of the compiler *)
Fixpoint aeval (st : state) (a : aexp) : nat := 
    match a with
    | ANum n => n
    | AId id => st id
    | APlus n m => (aeval st n) + (aeval st m)
    | AMult n m => (aeval st n) * (aeval st m)
    | AMinus n m => (aeval st n) - (aeval st m)
    end.

Lemma s_execute_app: forall st is1 is2 l,
  s_execute st l (is1 ++ is2) = s_execute st (s_execute st l is1) is2.
Proof.
  intros st is1 is2.
  induction is1 as [| i is1'].
  -reflexivity.
  -intros l. induction i;
      simpl; apply IHis1'. 
Qed.

Theorem s_compile_correct_general : forall (st : state) (e : aexp) sk,
  s_execute st sk (s_compile e) = [ aeval st e ] ++ sk.
Proof.
  intros.
  generalize dependent sk.
  induction e;
  try(intros; simpl; auto);
  try(repeat rewrite s_execute_app);
  try(rewrite IHe1; rewrite IHe2; simpl);
  try rewrite plus_comm; try rewrite mult_comm; auto.
Qed.



Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_correct_general.
Qed.






















(*
    content:
    1. 使用标准库
    2. total map & partial map definition
    3. Total Maps
    4. Partial Maps
    

*)




(*使用标准库*)
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.



(* total map & partial map definition *)
(*
total map:
    include a "default" element to be returned when a 
    key being looked up doesn't exist.

partial map:
    return an option to indicate success or failure.
*)





Inductive id:Type :=
  |Id : string -> id.


Definition beq_id id1 id2 :=
  match id1,id2 with
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_true_iff :
  forall x y : id,
  beq_id x y = true <-> x = y.
Admitted.

Theorem false_beq_id :
  forall x y : id,
  x <> y <-> beq_id x y = false.
Admitted.





(* Total Maps *)
(*----------------------------------------*)
(* 不用ADT,只用闭包实现数据类型 *)
Definition total_map (A : Type) := id -> A. (* type alias *)

Definition t_empty {A : Type} (v : A) : total_map A := 
    (fun _ => v).  (* default element *)

Definition t_update {A : Type} (m : total_map A) (x : id) (v : A) :=
    fun x' => if beq_id x x' then v else m x'.

Definition example_map := t_update (t_update (t_empty false) (Id "foo") false) 
                                   (Id "bar")
                                   true.

Lemma t_apply_empty :
    forall {A : Type} (x : id) (v : A), (t_empty v) x = v.
Proof.
  intros.
  unfold t_empty.
  reflexivity.
Qed.


Lemma beq_idP :
    forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros.
  destruct beq_id.
Admitted.

Theorem t_update_same :
    forall {X : Type} x (m : total_map X),
    t_update m x (m x) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  Admitted.








(* Partial Maps *)
(*-----------------------------------------*)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A:Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : id) (v : A) := 
    fun x' => if beq_id x x' then (Some v) else (m x').









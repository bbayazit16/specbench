From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

(* start imports *)
Require Import List.
Require Import Arith.
Import ListNotations.
(* end imports *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

Unset Hammer CVC4.
Unset Hammer Z3.

(* start prompt *)
(* 
  signature: "Definition generated_spec_is_empty (A: Type) (impl: list A -> bool) (l: list A) : Prop :="
  description: Implementation impl must return true if the list is empty, false otherwise.
  examples:
    - input: []
      output: true
    - input: [1]
      output: false
    - input: [1; 2; 3]
      output: false
    - input: ["hello"]
      output: false
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec_is_empty {A: Type} (impl: list A -> bool) (l: list A) : Prop :=
  impl l = match l with
           | [] => true
           | _ => false
           end.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_is_empty {A: Type} (impl: list A -> bool) (l: list A) : Prop :=
  impl l = Nat.eqb (length l) 0.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_is_empty:
  forall A impl,
  (forall l, @problem_spec_is_empty A impl l) <->
  (forall l, @generated_spec_is_empty A impl l).
Proof.
  hammer.
Qed.
(* end equivalence *)

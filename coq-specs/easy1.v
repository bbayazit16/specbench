From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

(* start imports *)
Require Import ZArith.
Require Import Lia.
Require Import List.
Import ListNotations.

Open Scope Z_scope.
(* end imports *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

(* start prompt *)
(* 
  signature: "Definition generated_spec (impl: Z -> bool) (x: Z) : Prop :="
  description: Implementation impl must return true if `x` is positive, false otherwise.
  examples:
    - input: -3
      output: false
    - input: 4
      output: true
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec (impl: Z -> bool) (x: Z) : Prop :=
  impl x = true <-> x > 0.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec (impl: Z -> bool) (x: Z) : Prop :=
  impl x = Z.ltb 0 x.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_equivalence:
forall impl,
(forall x, problem_spec impl x) ->
(forall x, generated_spec impl x).
Proof.
  hammer.
Qed.
  
(* end equivalence *)
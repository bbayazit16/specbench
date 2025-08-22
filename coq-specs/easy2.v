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
  signature: "Definition generated_spec (impl: bool -> bool -> bool) (b1 b2: bool) : Prop :="
  description: Implementation impl must return the XOR of the two boolean values.
  examples:
    - input: true, false
      output: true
    - input: true, true
      output: false
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec (impl: bool -> bool -> bool) (b1 b2: bool) : Prop :=
  exists r,
    impl b1 b2 = r /\
    r = if b1 then negb b2 else b2.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec (impl: bool -> bool -> bool) (b1 b2: bool) : Prop :=
  impl b1 b2 = xorb b1 b2.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_equivalence :
  forall impl, (forall b1 b2, problem_spec impl b1 b2) <->
               (forall b1 b2, generated_spec impl b1 b2).
Proof.
    hammer.
Qed.
(* end equivalence *)
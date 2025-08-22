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
  signature: "Definition generated_spec_next_light (impl: TrafficLight -> TrafficLight) (current: TrafficLight) : Prop :="
  description: Implementation impl must return the next traffic light in the cycle: Red -> Green -> Yellow -> Red.
  examples:
    - input: Red
      output: Green
    - input: Green
      output: Yellow
    - input: Yellow
      output: Red
*)
(* end prompt *)

(* start context *)
Inductive TrafficLight : Type :=
  | Red
  | Yellow
  | Green.

Definition traffic_light_eqb (t1 t2: TrafficLight) : bool :=
  match t1, t2 with
  | Red, Red => true
  | Yellow, Yellow => true
  | Green, Green => true
  | _, _ => false
  end.
(* end context *)

(* start problem_spec *)
Definition problem_spec_next_light (impl: TrafficLight -> TrafficLight) (current: TrafficLight) : Prop :=
  impl current = match current with
                 | Red => Green
                 | Green => Yellow
                 | Yellow => Red
                 end.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_next_light (impl: TrafficLight -> TrafficLight) (current: TrafficLight) : Prop :=
  impl current = if traffic_light_eqb current Red then Green
                 else if traffic_light_eqb current Green then Yellow
                 else Red.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_next_light:
  forall impl,
  (forall t, problem_spec_next_light impl t) <->
  (forall t, generated_spec_next_light impl t).
Proof.
  hammer.
Qed.
(* end equivalence *)

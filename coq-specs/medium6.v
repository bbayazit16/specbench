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
  signature: "Definition generated_spec_contains (impl: nat -> list nat -> bool) (n: nat) (l: list nat) : Prop :="
  description: Implementation impl must return true if the given number is contained in the list, false otherwise.
  examples:
    - input: n=5, l=[1; 2; 3; 4; 5]
      output: true
    - input: n=0, l=[1; 2; 3]
      output: false
    - input: n=2, l=[2]
      output: true
    - input: n=7, l=[]
      output: false
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec_contains (impl: nat -> list nat -> bool) (n: nat) (l: list nat) : Prop :=
  impl n l = if in_dec Nat.eq_dec n l then true else false.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_contains (impl: nat -> list nat -> bool) (n: nat) (l: list nat) : Prop :=
  impl n l = existsb (Nat.eqb n) l.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_contains:
  forall impl,
  (forall n l, problem_spec_contains impl n l) <->
  (forall n l, generated_spec_contains impl n l).
Proof.
  hammer.
Qed.
(* end equivalence *)

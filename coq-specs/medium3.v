From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

(* start imports *)
Require Import List.
Import ListNotations.
(* end imports *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

Unset Hammer CVC4.
Unset Hammer Z3.

(* start prompt *)
(* 
  signature: "Definition generated_spec_drop (A: Type) (impl: nat -> list A -> list A) (n: nat) (l: list A) : Prop :="
  description: Implementation impl must drop the first n elements from the list, returning the remaining suffix.
  examples:
    - input: 2, [1; 2; 3; 4; 5]
      output: [3; 4; 5]
    - input: 0, [1; 2; 3]
      output: [1; 2; 3]
    - input: 5, [1; 2]
      output: []
    - input: 3, []
      output: []
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec_drop (A: Type)
  (impl: nat -> list A -> list A)
  (n: nat) (l: list A) : Prop :=
  impl n l = skipn n l.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_drop (A: Type)
  (impl: nat -> list A -> list A)
  (n: nat) (l: list A) : Prop :=
  impl n l = 
    (fix drop (m: nat) (lst: list A) : list A :=
       match m, lst with
       | 0%nat, _ => lst
       | _, [] => []
       | S m', _ :: t => drop m' t
       end) n l.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_drop:
  forall (A: Type) impl,
  (forall n l, problem_spec_drop A impl n l) <->
  (forall n l, generated_spec_drop A impl n l).
Proof.
  hammer.
Qed.
(* end equivalence *)

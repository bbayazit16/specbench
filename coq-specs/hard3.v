From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

(* start imports *)
Require Import List.
Import ListNotations.
(* end imports *)

Unset Hammer CVC4.
Unset Hammer Z3.

(* start prompt *)
(* 
  signature: "Definition generated_spec_duplicate {A: Type} (impl: list A -> list A) (l: list A) : Prop :="
  description: Implementation impl must create a list where each element appears twice consecutively. For each element in the input list, the output should contain that element followed immediately by itself.
  examples:
    - input: [1; 2; 3]
      output: [1; 1; 2; 2; 3; 3]
    - input: []
      output: []
    - input: [5]
      output: [5; 5]
    - input: ["a"; "b"]
      output: ["a"; "a"; "b"; "b"]
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec_duplicate {A: Type}
  (impl: list A -> list A)
  (l: list A) : Prop :=
  impl l = flat_map (fun x => [x; x]) l.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_duplicate {A: Type}
  (impl: list A -> list A)
  (l: list A) : Prop :=
  impl l =
    (fix dup (lst: list A) : list A :=
       match lst with
       | [] => []
       | h :: t => h :: h :: dup t
       end) l.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_duplicate:
  forall A impl,
  (forall l, @problem_spec_duplicate A impl l) <->
  (forall l, @generated_spec_duplicate A impl l).
Proof.
  hammer.
Qed.
(* end equivalence *)

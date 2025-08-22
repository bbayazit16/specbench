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
  signature: "Definition generated_spec_append (A: Type) (impl: list A -> list A -> list A) (l1 l2: list A) : Prop :="
  description: Implementation impl must append two lists, returning the concatenation of the first list followed by the second.
  examples:
    - input: [1;2], [3;4]
      output: [1;2;3;4]
    - input: [], [1;2]
      output: [1;2]
    - input: [1;2], []
      output: [1;2]
    - input: [], []
      output: []
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec_append {A: Type}
  (impl: list A -> list A -> list A)
  (l1 l2: list A) : Prop :=
  impl l1 l2 = l1 ++ l2.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_append {A: Type}
  (impl: list A -> list A -> list A)
  (l1 l2: list A) : Prop :=
  impl l1 l2 = 
    (fix append (lst1 lst2: list A) : list A :=
       match lst1 with
       | [] => lst2
       | h :: t => h :: append t lst2
       end) l1 l2.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_append:
  forall (A: Type) impl,
  (forall l1 l2, @problem_spec_append A impl l1 l2) <->
  (forall l1 l2, @generated_spec_append A impl l1 l2).
Proof.
  hammer.
Qed.
(* end equivalence *)

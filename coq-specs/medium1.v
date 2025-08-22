From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

(* start prompt *)
(* 
  signature: "Definition generated_spec (A: Type) (impl: option A -> option A -> option A) (o1 o2: option A) : Prop :="
  description: Implementation impl must return the first option if it contains a value, otherwise return the second option.
  examples:
    - input: Some v1, Some v2 (for any values v1, v2 of type A)
      output: Some v1
    - input: Some v, None (for any value v of type A)
      output: Some v
    - input: None, Some v (for any value v of type A)
      output: Some v
    - input: None, None
      output: None
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec (A: Type) (impl: option A -> option A -> option A) (o1 o2: option A) : Prop :=
  let r := impl o1 o2 in
  (exists v, o1 = Some v /\ r = Some v) \/
  (o1 = None /\ r = o2).
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec (A: Type) (impl: option A -> option A -> option A) (o1 o2: option A) : Prop :=
  impl o1 o2 = match o1 with Some v => Some v | None => o2 end.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_equiv_first :
  forall (A: Type) impl, (forall o1 o2, problem_spec A impl o1 o2) <->
                         (forall o1 o2, generated_spec A impl o1 o2).
Proof. hammer. Qed.
(* end equivalence *)

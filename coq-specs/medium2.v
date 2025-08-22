From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

(* start prompt *)
(* 
  signature: "Definition generated_spec (A B C: Type) (f: A -> B -> C) (impl: option A -> option B -> option C) (oa: option A) (ob: option B) : Prop :="
  description: Implementation impl must apply function f to the values inside two options if both contain values, otherwise return None.
  examples:
    - input: Some a, Some b (for any values a, b and function f)
      output: Some (f a b)
    - input: Some a, None (for any value a and function f)
      output: None
    - input: None, Some b (for any value b and function f)
      output: None
    - input: None, None (for any function f)
      output: None
*)
(* end prompt *)

(* start problem_spec *)
Definition problem_spec (A B C: Type) (f: A -> B -> C) (impl: option A -> option B -> option C) (oa: option A) (ob: option B) : Prop :=
  let r := impl oa ob in
  (exists a b, oa = Some a /\ ob = Some b /\ r = Some (f a b)) \/
  ((oa = None \/ ob = None) /\ r = None).
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec (A B C: Type) (f: A -> B -> C) (impl: option A -> option B -> option C) (oa: option A) (ob: option B) : Prop :=
  impl oa ob =
    match oa with
    | None => None
    | Some a =>
        match ob with None => None | Some b => Some (f a b) end
    end.
(* end generated_spec *)

(* start equivalence *)
Theorem spec_equiv :
  forall (A B C: Type) (f: A -> B -> C) impl, 
    (forall oa ob, problem_spec A B C f impl oa ob) <->
    (forall oa ob, generated_spec A B C f impl oa ob).
Proof.
  hammer.
Qed.
(* end equivalence *)

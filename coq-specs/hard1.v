From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

Unset Hammer CVC4.
Unset Hammer Z3.

(* start prompt *)
(* 
  signature: "Definition generated_spec_route (impl : req -> resp) (r : req) : Prop :="
  description: Implementation impl must route HTTP requests to appropriate handlers based on method and path segments. Routes: GET Root/None -> HIndex (no auth), GET Users/None -> HListUsers (auth required), GET Users/Id -> HUser (auth required), GET Admin/* -> HAdminPanel (auth required), POST Users/None -> HListUsers (auth required), all other combinations -> HNotFound (no auth).
  examples:
    - input: {GET, Root, None}
      output: {HIndex, false}
    - input: {GET, Users, None}
      output: {HListUsers, true}
    - input: {GET, Users, Id}
      output: {HUser, true}
    - input: {GET, Admin, Settings}
      output: {HAdminPanel, true}
    - input: {POST, Users, None}
      output: {HListUsers, true}
    - input: {DELETE, Root, None}
      output: {HNotFound, false}
    - input: {PUT, Users, Id}
      output: {HNotFound, false}
    - input: {POST, Admin, None}
      output: {HNotFound, false}
*)
(* end prompt *)

(* start context *)
Inductive method := GET | POST | PUT | DELETE.
Inductive seg0 := Root | Users | Admin.
Inductive seg1 := None | Id | Settings.

Record req := { m : method; s0 : seg0; s1 : seg1 }.
Inductive handler := HIndex | HListUsers | HUser | HAdminPanel | HNotFound.
Record resp := { h : handler; requires_auth : bool }.
(* end context *)

(* start problem_spec *)
Definition problem_spec_route (impl : req -> resp) (r : req) : Prop :=
  exists out, impl r = out /\ 
  out = match r.(m), r.(s0), r.(s1) with
        | GET, Root,    None     => {| h := HIndex;      requires_auth := false |}
        | GET, Users,   None     => {| h := HListUsers;  requires_auth := true  |}
        | GET, Users,   Id       => {| h := HUser;       requires_auth := true  |}
        | GET, Admin,   _        => {| h := HAdminPanel; requires_auth := true  |}
        | POST, Users,  None     => {| h := HListUsers;  requires_auth := true  |}
        | _,   _,       _        => {| h := HNotFound;   requires_auth := false |}
        end.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_route (impl : req -> resp) (r : req) : Prop :=
  impl r = match r.(m), r.(s0), r.(s1) with
           | GET, Root,    None     => {| h := HIndex;      requires_auth := false |}
           | GET, Users,   None     => {| h := HListUsers;  requires_auth := true  |}
           | GET, Users,   Id       => {| h := HUser;       requires_auth := true  |}
           | GET, Admin,   _        => {| h := HAdminPanel; requires_auth := true  |}
           | POST, Users,  None     => {| h := HListUsers;  requires_auth := true  |}
           | _,   _,       _        => {| h := HNotFound;   requires_auth := false |}
           end.
(* end generated_spec *)

(* start equivalence *)
Theorem iso_route :
  forall impl, (forall r, problem_spec_route impl r) <-> (forall r, generated_spec_route impl r).
Proof. hammer. Qed.
(* end equivalence *)

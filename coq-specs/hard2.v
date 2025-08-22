From Hammer Require Import Hammer.
(* From Hammer Require Reconstr. *)

Set Hammer ATPLimit 16.
Set Hammer ReconstrLimit 32.

(* start imports *)
Require Import Bool.
(* end imports *)

Unset Hammer CVC4.
Unset Hammer Z3.

(* start prompt *)
(* 
  signature: "Definition generated_spec_file_access (impl: Permission -> FileType -> Operation -> bool) (perm: Permission) (ftype: FileType) (op: Operation) : Prop :="
  description: Implementation impl must determine file access permissions based on user permission level, file type, and requested operation. Owner can do everything except delete SystemFiles. GroupMember cannot access SystemFiles, can read/execute Executables, can read Documents but not write/delete them, and has full access to TempFiles. Other users can only read TempFiles and Documents, and execute Executables.
  examples:
    - input: Owner, Document, Write
      output: true
    - input: Owner, SystemFile, Delete
      output: false
    - input: GroupMember, Executable, Execute
      output: true
    - input: GroupMember, Document, Write
      output: false
    - input: Other, Document, Read
      output: true
    - input: Other, Document, Write
      output: false
    - input: Other, Executable, Execute
      output: true
*)
(* end prompt *)

(* start context *)
Inductive Permission : Type :=
  | Owner
  | GroupMember
  | Other.

Inductive FileType : Type :=
  | Executable
  | Document
  | SystemFile
  | TempFile.

Inductive Operation : Type :=
  | Read
  | Write
  | Execute
  | Delete.
(* end context *)

(* start problem_spec *)
Definition problem_spec_file_access
  (impl: Permission -> FileType -> Operation -> bool)
  (perm: Permission) (ftype: FileType) (op: Operation) : Prop :=
  impl perm ftype op =
    match perm with
    | Owner => match op with
               | Delete => negb (match ftype with SystemFile => true | _ => false end)
               | _ => true
               end
    | GroupMember => match ftype, op with
                     | SystemFile, _ => false
                     | Executable, Execute => true
                     | Executable, Read => true
                     | Executable, _ => false
                     | Document, Write => false
                     | Document, Delete => false
                     | Document, _ => true
                     | TempFile, Delete => true
                     | TempFile, _ => true
                     end
    | Other => match ftype, op with
               | TempFile, Read => true
               | Document, Read => true
               | Executable, Execute => true
               | _, _ => false
               end
    end.
(* end problem_spec *)

(* start generated_spec *)
Definition generated_spec_file_access
  (impl: Permission -> FileType -> Operation -> bool)
  (perm: Permission) (ftype: FileType) (op: Operation) : Prop :=
  impl perm ftype op =
    if match perm with Owner => true | _ => false end then
      if andb (match op with Delete => true | _ => false end)
              (match ftype with SystemFile => true | _ => false end) then
        false
      else true
    else if match perm with GroupMember => true | _ => false end then
      if match ftype with SystemFile => true | _ => false end then false
      else if match ftype with Executable => true | _ => false end then
        orb (match op with Execute => true | _ => false end)
            (match op with Read => true | _ => false end)
      else if match ftype with Document => true | _ => false end then
        andb (negb (match op with Write => true | _ => false end))
             (negb (match op with Delete => true | _ => false end))
      else (* TempFile *)
        true
    else (* Other *)
      orb (orb (andb (match ftype with TempFile => true | _ => false end)
                     (match op with Read => true | _ => false end))
               (andb (match ftype with Document => true | _ => false end)
                     (match op with Read => true | _ => false end)))
          (andb (match ftype with Executable => true | _ => false end)
                (match op with Execute => true | _ => false end)).
(* end generated_spec *)

(* start equivalence *)
Theorem spec_isomorphism_file_access:
  forall impl,
  (forall p f o, problem_spec_file_access impl p f o) <->
  (forall p f o, generated_spec_file_access impl p f o).
Proof.
  hammer.
Qed.
(* end equivalence *)

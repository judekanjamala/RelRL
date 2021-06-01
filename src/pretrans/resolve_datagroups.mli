(** resolve_datagroups.mli -- resolve (expand) datagroups *)

(** NOTE: The main function in this module, [resolve], must be run only after
    method specs have been fully expanded (to include all invariants, interface
    pre/post-conditions, and so on).  *)

open Annot

exception Resolve_datagroups_exn of string

(* [is_resolved e] checks whether [e] contains any image expressions that
   involve datagroups.  Currently, the only datagroup we support is [any]. *)
val is_resolved : effect -> bool

(* [resolve_effect c e] expands any image expression, in [e], of the form
   [G`any] to [G`f1...G`fn] where [f1...fn] are all known fields in class table
   [c]. *)
val resolve_effect : Ctbl.t -> effect -> effect

(* [resolve (c,p)] expands all effects and boundaries in program [p] using class
   table [c]. *)
val resolve : Ctbl.t * penv -> penv

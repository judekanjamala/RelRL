(** boundary_info.mli -- cache interface and module boundaries *)

open Annot

exception Unknown of string

exception Uninitialized

(** [boundary m] returns the boundary of interface/module/bimodule [m]. *)
val boundary : ident -> boundary_decl

(** [imported_boundaries m] returns the combined boundary of all interfaces and
    modules imported by [m]. *)
val imported_boundaries : ident -> boundary_decl

(** [overall_boundary m] combines the result of [boundary m] and
    [imported_boundaries m], ensuring that the result does not contain
    duplicates. *)
val overall_boundary : ident -> boundary_decl

(** [add p m frag] extends the current cache with information about the boundary
    of interface or module [m] in program [p]. *)
val add : penv -> ident -> program_elt -> unit

(** Initialization.  Needs to be run before any of the above functions can be
   used.  Otherwise, the Uninitialized error is raised. *)
val run : penv -> unit

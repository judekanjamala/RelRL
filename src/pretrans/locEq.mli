(** locEq.mli -- derive local equivalence specs *)

open Annot

exception Unknown_method of string

(** [derive_locEq c p m] returns the local equivalence spec for method [m],
    which is expected to be a method in some interface or module in program
    [p].  The optional flag [resolve] determines whether datagroups such as
    any are expanded when generating locEq specs.  In general, they should be,
    but specs are simpler to read and understand when resolve is set to false.*)
val derive_locEq : ?resolve:bool -> Ctbl.t -> penv -> ident -> bispec

(** [pp_derive_locEq c p m outf] pretty prints the local equivalence spec on
    [outf].  The optional flag [resolve] plays the same role as in
    [derive_locEq].*)
val pp_derive_locEq :
  ?resolve: bool -> Ctbl.t -> penv -> ident -> Format.formatter -> unit

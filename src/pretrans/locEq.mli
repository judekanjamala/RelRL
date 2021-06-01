(** locEq.mli -- derive local equivalence specs *)

open Annot

exception Unknown_method of string

(** [derive_locEq p m] returns the local equivalence spec for method [m].  [m]
    is expected to be a method in some interface or module in program [p]. *)
val derive_locEq : penv -> ident -> bispec

(** [pp_derive_locEq p m outf] pretty prints the local equivalence spec on
    [outf]. *)
val pp_derive_locEq : penv -> ident -> Format.formatter -> unit

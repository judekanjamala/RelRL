(** encap_check.mli -- encapsulation check *)

open Annot

exception Encap_check_fail of (atomic_command, exp t) result

(** Flag to determine whether the encap check must be performed.  Set to [true]
    by default. *)
val do_encap_check : bool ref

(** [run (c,p)] performs the encap check on all modules in [p], possibly raising
    [Encap_check_fail].  [c] is expected to be the class table corresponding to
    [p]. *)
val run : Ctbl.t * penv -> penv

(** [run_maybe_exit (c,p)] is the same as [run (c,p)], but exits the program
    with an error message if the encap check is determined (statically) to
    fail. *)
val run_maybe_exit : Ctbl.t * penv -> penv

(** Debug flag meant to be used during development. *)
val encap_debug : bool ref

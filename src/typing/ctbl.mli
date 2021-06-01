(* ctbl.mli -- class tables interface *)

open Astutil
open Annot

type t

val empty : t

val field_exists : t -> field:ident -> bool

val class_exists : t -> classname:ident -> bool

val field_names : t -> classname:ident -> ident list

val fields : t -> classname:ident -> (ident * ity) list

val annot_fields : t -> classname:ident -> ident Annot.t list

val known_classes : t -> class_decl list

val known_class_names : t -> ident list

val known_field_names : t -> ident list

val known_fields : t -> field_decl list

val decl_class : t -> field:ident -> ident option

val field_type : t -> field:ident -> ity option

val field_attr : t -> field:ident -> modifier option

val is_ghost_field : t -> field:ident -> bool

val is_array_like_class : t -> classname:ident -> bool

val element_type : t -> classname:ident -> ity option

val array_like_length_field : t -> classname:ident -> (ident * ity) option

val array_like_slots_field : t -> classname:ident -> (ident * ity) option

val add : t -> ?base_ty:ity -> class_decl -> t

val update : t -> class_decl -> t

val union : t -> t -> t

val qualify_ctbl : t -> string -> t

val of_interface_def : interface_def -> t

val of_module_def : module_def -> t

val of_penv : program_elt M.t -> t

val debug_print_ctbl : out_channel -> t -> unit

(** boundary_info.ml -- cache interface and module boundaries *)

open Astutil
open Annot
open Lib

exception Unknown of string
exception Uninitialized


(* Let I be an interface, M be a module, a BM be a bimodule.

   current(I)  = boundary of I
   current(M)  = current(Interface(M))
   current(BM) = current(LeftModule(BM))

   imported(I)  = boundaries of all interfaces import by I
   imported(M)  = boundaries of all interfaces/modules imported by M
                + imported(Interface(M))
   imported(BM) = imported(LeftModule(BM)) + imported(RightModule(BM))

*)
type boundary_info = {
  current: boundary_decl;
  imported: boundary_decl;
}

type boundary_map = boundary_info M.t

let bmap : boundary_map option ref = ref None

let get_bmap () = match !bmap with
  | None -> raise Uninitialized
  | Some bmap -> bmap

let boundary_of_interface intr : boundary_decl =
  let ext = function Intr_boundary bnd -> Some bnd | _ -> None in
  concat_filter_map ext intr.intr_elts

let module_interface penv mdl : interface_def =
  let interface_name = mdl.mdl_interface in
  match M.find interface_name penv with
  | Unary_interface i -> i
  | _ | exception Not_found ->
    raise (Unknown (string_of_ident interface_name))

let boundary_of_module penv mdl : boundary_decl =
  boundary_of_interface (module_interface penv mdl)

let boundary_of_relation_module penv bimdl : boundary_decl =
  match M.find bimdl.bimdl_left_impl penv with
  | Unary_module m -> boundary_of_module penv m
  | _ | exception Not_found ->
    raise (Unknown (string_of_ident bimdl.bimdl_name))

let interface_imports, module_imports =
  let ext0 = function
    | {import_kind = Iregular; import_name} -> Some import_name
    | _ -> None in
  let exti = function Intr_import m -> ext0 m | _ -> None in
  let extm = function Mdl_import m -> ext0 m | _ -> None in
  (fun i -> List.filter_map exti i.intr_elts),
  (fun m -> List.filter_map extm m.mdl_elts)

let rec import_boundaries penv name : boundary_decl =
  let rec loop bnds imports = match imports with
    | [] -> bnds
    | m :: rest ->
      match M.find m penv with
      | Unary_interface i -> loop (boundary_of_interface i @ bnds) rest
      | Unary_module m -> loop (boundary_of_module penv m @ bnds) rest
      | _ | exception Not_found -> loop bnds rest in
  match M.find name penv with
  | Unary_interface i -> loop [] (interface_imports i)
  | Unary_module m ->
    let i = module_interface penv m in
    loop [] (module_imports m @ interface_imports i)
  | Relation_module b ->
    let l, r = b.bimdl_left_impl, b.bimdl_right_impl in
    import_boundaries penv l @ import_boundaries penv r
  | exception Not_found ->
    raise (Unknown (string_of_ident name))

let add_program_fragment penv name frag bndmap =
  let imported = normalize_boundary (import_boundaries penv name) in
  let add bndfn m bndmap =
    let current = check is_normalized_boundary (bndfn m) in
    M.add name {current; imported} bndmap in
  match frag with
  | Unary_interface i -> add boundary_of_interface i bndmap
  | Unary_module m -> add (boundary_of_module penv) m bndmap
  | Relation_module b -> add (boundary_of_relation_module penv) b bndmap

let add penv name frag =
  match !bmap with
  | None -> raise Uninitialized
  | Some m -> bmap := Some (add_program_fragment penv name frag m)

let boundary_map_of_penv prog : boundary_map =
  M.fold (add_program_fragment prog) prog M.empty

let get_binfo mdl =
  let bm = get_bmap () in
  try M.find mdl bm with
  | Not_found -> raise (Unknown (string_of_ident mdl))

let boundary mdl = (get_binfo mdl).current

let imported_boundaries mdl = (get_binfo mdl).imported

let overall_boundary mdl =
  let {current; imported} = get_binfo mdl in
  nub (current @ imported)

let run penv = bmap := Some (boundary_map_of_penv penv)

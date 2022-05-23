(* ctbl.ml -- defines class tables *)

open Lib
open Astutil
open Annot
open Option
open Option.Monad_syntax

type class_info = {
  name: classname;
  fields: field_decl list;
}

let info_of_decl ?(base_ty=None) cdecl =
  { name = cdecl.class_name;
    fields = cdecl.fields;
  }

let decl_of_info cinfo = {class_name = cinfo.name; fields = cinfo.fields}

let merge_cdecl c1 c2 =
  assert (c1.class_name = c2.class_name);
  let fields = ref [] in
  List.iter (fun fdecl ->
      if List.mem fdecl !fields then ()
      else fields := fdecl :: !fields
    ) (c1.fields @ c2.fields);
  info_of_decl { class_name = c1.class_name; fields = !fields }

let fieldnames cinfo = List.map (fun e -> e.field_name.node) cinfo.fields

type t = class_info M.t

let empty : t = M.empty

let field_exists tbl ~field:f =
  M.exists (fun _ cdecl -> List.mem f (fieldnames cdecl)) tbl

let class_exists tbl ~classname:c = M.mem c tbl

let class_infos tbl = List.map snd (M.bindings tbl)

let known_classes tbl = List.map decl_of_info (class_infos tbl)

let known_class_names tbl = List.map fst (M.bindings tbl)

let field_names tbl ~classname:c =
  if class_exists tbl c
  then fieldnames (M.find c tbl)
  else failwith ("field_names: unknown class " ^ string_of_ident c)

let fields tbl ~classname:c =
  if not (class_exists tbl c)
  then failwith ("fields: unknown class " ^ string_of_ident c)
  else begin
    let cinfo = M.find c tbl in
    List.map (fun f -> (f.field_name.node, f.field_ty)) cinfo.fields
  end

let field_with_suffix target fname =
  let suffix n str =
    let len = String.length str in
    if n > len then None
    else Some (String.sub str (len - n) n) in
  let fname = match fname with
    | Ast.Id name -> name
    | _ -> invalid_arg "field_with_suffix" in
  let fname = String.lowercase_ascii fname in
  let len = String.length target in
  match suffix len fname with
  | None -> false
  | Some inner -> inner = target

(* Check if class c contains at least 2 fields -- one with the suffix "length"
   and the other with the suffix "slots" *)
let is_array_like_class tbl ~classname:c =
  let flds   = fields tbl c in
  let length = List.find_opt (field_with_suffix "length" % fst) flds in
  let slots  = List.find_opt (field_with_suffix "slots"  % fst) flds in
  List.length flds >= 2
  && match length, slots with
  | Some (_, Tint), Some (_, Tmath (Id "array", Some _)) -> true
  | _ -> false

let element_type tbl ~classname:c =
  if not (is_array_like_class tbl c)
  then invalid_arg "element_type: expected an array-like class"
  else
    let f = List.find (field_with_suffix "slots" % fst) (fields tbl c) in
    match f with
    | (_, Tmath (Id "array", Some ty)) -> Some ty
    | _ -> None

let array_like_length_field tbl ~classname:c =
  if not (is_array_like_class tbl c)
  then invalid_arg "array_like_length_field: expected an array-like class"
  else List.find_opt (field_with_suffix "length" % fst) (fields tbl c)

let array_like_slots_field tbl ~classname:c =
  if not (is_array_like_class tbl c)
  then invalid_arg "array_like_slots_field: expected an array-like class"
  else List.find_opt (field_with_suffix "slots" % fst) (fields tbl c)

let annot_fields tbl ~classname:c =
  let fields = fields tbl c in
  List.map (fun (f, fty) -> f -: fty) fields

let known_fields tbl = M.fold (fun _ v vs -> v.fields @ vs) tbl []

let known_field_names tbl = concat_map fieldnames (class_infos tbl)

let get_field_info tbl ~field:f : (ident * field_decl) option =
  M.fold (fun cname {fields=flds;_} res ->
      let fldnames = List.map (fun e -> e.field_name.node) flds in
      if List.mem f fldnames
      then Some (cname, List.find (fun e -> e.field_name.node = f) flds)
      else res
    ) tbl None

let decl_class tbl ~field:f =
  let* cname, _ = get_field_info tbl f in
  some cname

let field_type tbl ~field:f =
  let* _, {field_ty; _} = get_field_info tbl f in
  some field_ty

let field_attr tbl ~field:f =
  let* _, {attribute; _} = get_field_info tbl f in
  some attribute

let is_ghost_field tbl ~field:f =
  let ty = field_type tbl f in
  let attr = field_attr tbl f in
  ty = Some Trgn || attr = Some Ghost

let add tbl ?base_ty cdecl =
  let cname = cdecl.class_name in
  if M.mem cname tbl then begin
    let ex_cinfo = M.find cname tbl in
    let ex_cdecl = decl_of_info ex_cinfo in
    let updated  = merge_cdecl ex_cdecl cdecl in
    M.add cname updated (M.remove cname tbl)
  end else M.add cname (info_of_decl cdecl ~base_ty:base_ty) tbl

let update tbl cdecl =
  assert (class_exists tbl cdecl.class_name);
  M.update cdecl.class_name (function
      | Some cinfo -> Some (info_of_decl cdecl)
      | None -> assert false
    ) tbl

let union =
  let merge_fn k v1 v2 =
    let v1' = decl_of_info v1 and v2' = decl_of_info v2 in
    Some (merge_cdecl v1' v2') in
  M.union merge_fn

let of_interface_def {intr_name; intr_elts} : t =
  let tbl = empty in
  List.fold_left (fun map elt ->
      match elt with
      | Intr_cdecl cdecl -> add map cdecl
      | _ -> map
    ) tbl intr_elts

let of_module_def mdl : t =
  let tbl = empty in
  List.fold_left (fun map elt ->
      match elt with
      | Mdl_cdef (Class cdecl) -> add map cdecl
      | _ -> map
    ) tbl mdl.mdl_elts

let of_penv penv : t =
  let tbl = empty in
  M.fold (fun name prog tbl ->
      match prog with
      | Unary_interface idef -> union (of_interface_def idef) tbl
      | Unary_module mdef -> union (of_module_def mdef) tbl
      | _ -> tbl
    ) penv tbl

let qualify_cdecl (cdecl: class_decl) qual : class_decl =
  let qualify_fdecl fdecl =
    let {field_name; field_ty; attribute} = fdecl in
    let name = qualify_ident field_name.node (some qual) in
    {field_name = {node=name; ty=field_name.ty};
     field_ty = qualify_ity field_ty qual;
     attribute = attribute} in
  let fields = List.map qualify_fdecl cdecl.fields in
  { cdecl with fields }

let qualify_ctbl (ctbl: t) (qual: string) : t =
  M.fold (fun k v tbl ->
      let qk = qualify_ident k (Some qual) in
      let v = decl_of_info v in
      M.add qk (info_of_decl (qualify_cdecl v qual)) tbl
    ) ctbl empty

let debug_print_ctbl outf (t: t) =
  let show_cinfo cname cinfo =
    let cname = string_of_ident cname in
    let flds = cinfo.fields in
    let strs = List.map (fun finfo ->
        string_of_ident finfo.field_name.node
        ^ ": "
        ^ string_of_ity finfo.field_ty
      ) flds in
    let strs = String.concat "; " strs in
    Printf.fprintf outf "%s{ %s }" cname strs in
  let bindings = M.bindings t in
  List.iter (fun (cname, cinfo) ->
      Printf.fprintf outf "  ";
      show_cinfo cname cinfo;
      Printf.fprintf outf "\n";
    ) bindings; Printf.fprintf outf "\n"

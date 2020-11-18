(* translate.ml -- translate source language to Why3 parse trees *)

open Ast
open Astutil
open Lib
open Typing
open Pretrans
open Pretty

open Why3
open Why3util
open Build_operators


let trans_debug = ref false

(* -------------------------------------------------------------------------- *)
(* Constants -- expected to be in scope                                       *)
(* -------------------------------------------------------------------------- *)

(* See <WHYREL-STDLIB/prelude.mlw *)

let old_fn : Ptree.qualid = mk_qualid ["old"]

(* null : reference *)
let null_const : Ptree.expr = mk_evar (mk_ident "null")
(* let null_const_term : Ptree.term = mk_var (mk_ident "nullConst") *)
let null_const_term : Ptree.term = mk_var (mk_ident "null")

let empty_rgn : Ptree.qualid = mk_qualid ["emptyRgn"]

let eq_rgn_fn  : Ptree.qualid = mk_qualid ["eqRgn"]
let eq_bool_fn : Ptree.qualid = mk_qualid ["eqBool"]
let eq_unit_fn : Ptree.qualid = mk_qualid ["eqUnit"]

(* Functions from Why3's standard library for binary operators *)
let div_fn    : Ptree.qualid = mk_qualid ["div"]
let union_fn  : Ptree.qualid = mk_qualid ["Rgn"; "union"]
let inter_fn  : Ptree.qualid = mk_qualid ["Rgn"; "inter"]
let diff_fn   : Ptree.qualid = mk_qualid ["Rgn"; "diff"]
let mem_fn    : Ptree.qualid = mk_qualid ["Rgn"; "mem"]
let subset_fn : Ptree.qualid = mk_qualid ["Rgn"; "subset"]
let mk_set_fn : Ptree.qualid = mk_qualid ["Rgn"; "mk"]
let singleton_fn : Ptree.qualid = mk_qualid ["singleton"]
let disjoint_fn : Ptree.qualid = mk_qualid [Ident.op_infix "\\#"]

(* Functions acting on finite maps (see <WHY3_STDLIB>/fmap.mlw) *)
let map_mem_fn    : Ptree.qualid = mk_qualid [Ident.op_infix "\\:"]
let map_find_fn   : Ptree.qualid = mk_qualid [Ident.op_get ""]
let map_add_fn    : Ptree.qualid = mk_qualid ["M"; "add"]
let map_create_fn : Ptree.qualid = mk_qualid ["M"; "create"]

let map_mem map k   : Ptree.expr = map_mem_fn <$> [k; map]

let map_find map k  : Ptree.expr =
  let find_fn = mk_qualid [Ident.op_get ""] in
  find_fn <$> [map; k]

let map_add map k v : Ptree.expr = map_add_fn <$> [k; v; map]
let map_empty_expr  : Ptree.expr = map_create_fn <$> [mk_expr (Etuple [])]

(* Functions acting on arrays
   Assume:
   aget  : array 'a -> int -> 'a           = Array.([])
   aset  : array 'a -> int -> 'a -> unit   = Array.([]<-)
   amake : int -> 'a -> array 'a           = Array.make
*)
let array_get_fn  : Ptree.qualid = mk_qualid ["A"; "get"]
let array_set_fn  : Ptree.qualid = mk_qualid ["A"; "set"]
let array_make_fn : Ptree.qualid = mk_qualid ["A"; "make"]
let array_len_fn  : Ptree.qualid = mk_qualid ["A"; "length"]

(* ``Type'' predicate
   typeof_rgn : state -> rgn -> reftype -> <prop>
*)
let typeof_rgn_fn : Ptree.qualid = mk_qualid ["typeofRgn"]

let get_ref_fn : Ptree.qualid = mk_qualid [Ident.op_prefix "!"]
let set_ref_fn : Ptree.qualid = mk_qualid [Ident.op_infix ":="]

(* Source language locals are Why3 local references *)
let get_ref id : Ptree.expr = mk_eapp get_ref_fn [mk_qevar id]

let get_ref_term id : Ptree.term = mk_tapp get_ref_fn [mk_qvar id]

let set_ref id expr : Ptree.expr = mk_eapp set_ref_fn [mk_qevar id; expr]

let mk_ref_fn : Ptree.qualid = mk_qualid ["ref"]

(* Why3's ``old'' function *)
let mk_old_term t = mk_term (Tapply (mk_var (mk_ident "old"), t))

(* Import Prelude from WhyRel's stdlib.  Expects <WHYREL-STDLIB> to be
   in Why3's library search path. *)
let import_prelude : Ptree.decl = use_import ["prelude"; "Prelude"]

(* Import Refperm module from WhyRel's stdlib. *)
let import_refperm : Ptree.decl = use_import ["prelude"; "PreRefperm"]

(* Refperm related *)
let id_ref_fn : Ptree.qualid = mk_qualid ["PreRefperm"; "idRef"]
let id_rgn_fn : Ptree.qualid = mk_qualid ["PreRefperm"; "idRgn"]
let update_refperm : Ptree.qualid = mk_qualid ["PreRefperm"; "updateRefperm"]
let invert_refperm : Ptree.qualid = mk_qualid ["PreRefperm"; "invert"]


(* Initial label *)
let init_label = mk_ident "INIT"


(* -------------------------------------------------------------------------- *)
(* Auxiliary functions on identifiers                                         *)
(* -------------------------------------------------------------------------- *)

(* Conventions

   1. Each source language class name is a constructor for
      ``reftype''.  The constructor for class "klass" is "Klass" and
      the constructor for class "M::klass" is "M_klass".  Note that
      Why3 constructors must start with a capital letter.
   2. Each field is translated to a Why3 identifier by prefixing it
      with its class name (lowercased) followed by an underscore.
      Therefore, field ``f'' of class ``Klass'' is translated to
      ``klass_f''.
*)

let maybe_underscore_with fn name =
  match name with
  | Id cname -> fn cname
  | Qualid (hd, qs) ->
    String.concat "_" @@ fn hd :: qs

let unqualify_ident = maybe_underscore_with (fun s -> s)

let capitalize_and_maybe_underscore =
  maybe_underscore_with String.capitalize_ascii

let lowercase_and_maybe_underscore =
  maybe_underscore_with String.lowercase_ascii

let mk_reftype_ctor cname : Ptree.ident =
  mk_ident @@ capitalize_and_maybe_underscore cname

let mk_field_str cname field_name : string =
  let cname = lowercase_and_maybe_underscore cname in
  cname ^ "_" ^ unqualify_ident field_name

let mk_field_ident cname field_name : Ptree.ident =
  mk_ident @@ mk_field_str cname field_name

let mk_ctor_name cname : Ptree.ident =
  mk_ident @@ "init_" ^ capitalize_and_maybe_underscore cname

let mk_alloc_name cname : Ptree.ident =
  let name = mk_reftype_ctor cname in
  mk_ident @@ "mk_" ^ name.id_str

let id_name id : string =
  match id with
  | Id name  -> name
  | Qualid _ -> invalid_arg ("id_name: " ^ string_of_ident id)


(* -------------------------------------------------------------------------- *)
(* Translation contexts                                                       *)
(* -------------------------------------------------------------------------- *)

(* ident_kind is required since how we access or update the value
   referred to by an identifier may be different depending on whether
   the identifier is global, local, a parameter, a predicate, and so on.
*)
type ident_kind =
  | Id_local of ity
  | Id_global
  | Id_logic    (* introduced by let, forall, and exists *)
  | Id_other    (* methods, parameters, predicates, axioms, and lemmas *)
  | Id_extern   (* extern methods, predicates, axioms and lemmas *)

(* Invariant:

   Let (k, id) be an item in ident_map.  Then,
      k = Id_local  ==> id = Qident id_name
      k = Id_global ==> id = Qident id_name

   If (f, f') is in field_map, then f' = mk_field_ident k f where
   k = DeclClass(f)
*)
type ctxt = {
  ctbl: Ctbl.t;
  (* Source language identifiers to Why3 qualids *)
  ident_map: (ident_kind * Ptree.qualid) IdentM.t;
  (* Field names to Why3 identifiers *)
  field_map: Ptree.ident IdentM.t;
  (* Classes instantiated by a method.  Also keeps track of classes instantiated
     by callees. *)
  inst_map: IdentS.t IdentM.t;
  (* Extern types with their default *)
  extty_map: ident IdentM.t;
  (* Write effects for generated Why3 methods *)
  meth_wrs: QualidS.t QualidM.t;
  (* Current module or interface *)
  current_mdl: ident option;
}

(* FIXME: inst_map may not be required anymore since we also have meth_wrs. *)

(* FIXME IMPORTANT -- BUG

   If the source language contains two different identifiers called
   ``name'' and ``Name'' then they will be mapped to the same Why3
   identifier.

   27 Aug 2020: This comment may not be accurate; to test.
*)

let ini_ctxt =
  let ini_ident_map = IdentM.of_seq @@ List.to_seq
      [ Id "alloc",  (Id_global, mk_qualid ["alloct"]);
        Id "make",   (Id_other, array_make_fn);
        Id "get",    (Id_other, array_get_fn);
        Id "set",    (Id_other, array_set_fn);
        Id "length", (Id_other, array_len_fn);
      ] in
  { ctbl = Ctbl.empty;
    ident_map = ini_ident_map;
    field_map = IdentM.empty;
    extty_map = IdentM.empty;
    inst_map = IdentM.empty;
    meth_wrs = QualidM.empty;
    current_mdl = None;
  }

type bi_ctxt = {
  (* Left context *)
  left_ctxt: ctxt;
  (* Right context *)
  right_ctxt: ctxt;
  (* Qualified ident of left state *)
  left_state: Ptree.qualid;
  (* Qualified ident of right state *)
  right_state: Ptree.qualid;
  (* Qualified ident of refperm *)
  refperm: Ptree.qualid;
  (* List of known bipredicates *)
  bipreds: Ptree.qualid list;
  (* Bimethods along with their write effects *)
  bimethods: (Ptree.qualid * QualidS.t) IdentM.t;
  (* Current bimodule *)
  current_bimdl: (ident * ident * ident) option;
}

let ini_bi_ctxt =
  { left_ctxt  = ini_ctxt;
    right_ctxt = ini_ctxt;
    left_state = mk_qualid [""];
    right_state = mk_qualid [""];
    refperm = mk_qualid [""];
    bipreds = [];
    bimethods = IdentM.empty;
    current_bimdl = None }

let merge_ctxt c c' =
  let merge_fn _ s _ = Some s in
  let ctbl = Ctbl.union c.ctbl c'.ctbl in
  let ident_map = IdentM.union merge_fn c.ident_map c'.ident_map in
  let field_map = IdentM.union merge_fn c.field_map c'.field_map in
  let extty_map = IdentM.union merge_fn c.extty_map c'.extty_map in
  let inst_map = IdentM.union merge_fn c.inst_map c'.inst_map in
  let meth_wrs = QualidM.union merge_fn c.meth_wrs c'.meth_wrs in
  let current_mdl = c.current_mdl in
  {ctbl; ident_map; field_map; extty_map; inst_map; meth_wrs; current_mdl}

let merge_bi_ctxt c c' =
  let merge_fn _ s _ = Some s in
  let left_ctxt = merge_ctxt c.left_ctxt c'.left_ctxt in
  let right_ctxt = merge_ctxt c.right_ctxt c'.right_ctxt in
  let left_state = c.left_state in
  let right_state = c.right_state in
  let refperm = c.refperm in
  let bipreds = c.bipreds @ c'.bipreds in
  let bimethods = IdentM.union merge_fn c.bimethods c'.bimethods in
  let current_bimdl = c.current_bimdl in
  {left_ctxt; right_ctxt; left_state; right_state; refperm; bipreds;
   bimethods; current_bimdl}

let qualify_ctxt ctxt name =
  let idt_map = ctxt.ident_map in
  let ini_map = ini_ctxt.ident_map in
  let ident_map = IdentM.fold (fun k v new_map ->
      match v with
      | Id_other, v_name when not (IdentM.mem k ini_map) ->
        let vs = string_list_of_qualid v_name in
        let v_name' = mk_qualid (name :: vs) in
        IdentM.add k (Id_other, v_name') new_map
      | Id_extern, v_name ->
        let vs = string_list_of_qualid v_name in
        let v_name' = mk_qualid (name :: vs) in
        IdentM.add k (Id_extern, v_name') new_map
      | _ -> IdentM.add k v new_map
    ) idt_map IdentM.empty in
  let meth_wrs = QualidM.fold (fun k v new_map ->
      let k' = mk_qualid (name :: string_list_of_qualid k) in
      QualidM.add k' v new_map
    ) ctxt.meth_wrs QualidM.empty in
  {ctxt with ident_map; meth_wrs}

let qualify_bi_ctxt bi_ctxt name =
  let left_ctxt = qualify_ctxt bi_ctxt.left_ctxt name in
  let right_ctxt = qualify_ctxt bi_ctxt.right_ctxt name in
  let bimethods = IdentM.fold (fun k (vname,vset) new_map ->
      let vname = mk_qualid (name :: string_list_of_qualid vname) in
      IdentM.add k (vname,vset) new_map
    ) bi_ctxt.bimethods IdentM.empty in
  {bi_ctxt with left_ctxt; right_ctxt; bimethods }

let ctxt_locals ctxt : (ident * (ity * Ptree.qualid)) list =
  let open IdentM in
  let extract = function (Id_local t, id) -> (t, id) | _ -> assert false in
  let is_local _ (knd, _) = match knd with Id_local _ -> true | _ -> false in
  bindings (map extract (filter is_local ctxt.ident_map))

let lookup_id ctxt state id : Ptree.expr =
  if id = Id "alloc" then
    let state_id = ident_of_qualid state in
    let target = mk_qualid [state_id.Ptree.id_str; "alloct"; "M"; "domain"] in
    mk_qevar target
  else match IdentM.find id ctxt.ident_map with
    | Id_local _, (Qident _ as id') -> get_ref id'
    | Id_local _, _ ->
      invalid_arg "lookup_id: local associated with qualified ident"
    | Id_global, Qident id' -> mk_qevar (Qdot (state, id'))
    | Id_global, _ ->
      invalid_arg "lookup_id: global associated with qualified ident"
    | _, id -> mk_qevar id
    | exception Not_found ->
      failwith @@ "Unknown identifier " ^ string_of_ident id

let lookup_id_term ctxt state id : Ptree.term =
  if id = Id "alloc" then
    let state_id = ident_of_qualid state in
    let target = mk_qualid [state_id.Ptree.id_str; "alloct"; "M"; "domain"] in
    mk_qvar target
  else match IdentM.find id ctxt.ident_map with
    | Id_local _, (Qident _ as id') -> get_ref_term id'
    | Id_local _, _ ->
      invalid_arg "lookup_id_term: local associated with qualified ident"
    | Id_global, Qident id' -> mk_qvar (Qdot (state, id'))
    | Id_global, _ ->
      invalid_arg "lookup_id_term: global associated with qualified ident"
    | _, id -> mk_qvar id
    | exception Not_found ->
      failwith @@ "Unknown identifier " ^ string_of_ident id

let lookup_field ctxt f =
  match IdentM.find f ctxt.field_map with
  | res -> res
  | exception Not_found ->
    failwith @@ "lookup_field: Unknown field " ^ string_of_ident f

let simple_resolve_field ctxt f =
  match IdentM.find f ctxt.field_map with
  | fld -> fld
  | exception Not_found -> ~. (id_name f)

let update_id ?msg ctxt state id e : Ptree.expr =
  let explain e =
    match msg with
    | None   -> e
    | Some m -> explain_expr e m in
  match IdentM.find id ctxt.ident_map with
  | Id_local _, (Qident _ as id') -> set_ref id' (explain e)
  | Id_local _, _ -> invalid_arg "update_id: qualified local"
  | Id_global, (Qident x) ->
    let e = explain e in
    mk_expr (Eassign [mk_qevar (state %. x), None, e])
  | Id_global, _ -> invalid_arg "update_id: qualified global"
  | Id_logic, _ ->  invalid_arg ("update_id: logic var " ^ string_of_ident id)
  | Id_other, _ ->  invalid_arg ("update_id: " ^ string_of_ident id)
  | Id_extern, _ -> invalid_arg ("update_id: " ^ string_of_ident id)
  | exception Not_found -> failwith ("Unknown: " ^ string_of_ident id)

(* To be used by functions that need to generate new identifiers, and
   not by functions that translate source trees to Why3 parse trees *)
let reset_fresh_id, mk_fresh_id =
  let stamp = ref 0 in
  (fun () -> stamp := 0), (fun str -> incr stamp; str ^ string_of_int !stamp)

(* FIXME: handle Qualid (id, ids) ? *)
let gen_ident state ctxt name : Ptree.ident =
  let open IdentM in
  let state_id = (ident_of_qualid state).Ptree.id_str in
  let rec loop name : Ptree.ident =
    let name' = Id name in
    if mem name' ctxt.ident_map || mem name' ctxt.field_map || name = state_id
    then loop (mk_fresh_id name)
    else mk_ident name in
  loop name

let gen_ident2 bi_ctxt name : Ptree.ident =
  let open IdentM in
  let lstate = (ident_of_qualid bi_ctxt.left_state).Ptree.id_str in
  let rstate = (ident_of_qualid bi_ctxt.right_state).Ptree.id_str in
  let refperm = (ident_of_qualid bi_ctxt.refperm).Ptree.id_str in
  let rec loop name : Ptree.ident =
    let name' = Id name in
    if mem name' bi_ctxt.left_ctxt.ident_map
    || mem name' bi_ctxt.right_ctxt.ident_map
    || mem name' bi_ctxt.left_ctxt.field_map
    || mem name' bi_ctxt.right_ctxt.field_map
    || name = lstate || name = rstate || name = refperm
    then loop (mk_fresh_id name)
    else mk_ident name in
  loop name

let fresh_name ctxt name : string =
  let rec loop name : Ptree.ident =
    let name' = Id name in
    if IdentM.mem name' ctxt.ident_map || IdentM.mem name' ctxt.field_map
    then loop (mk_fresh_id name)
    else mk_ident name in
  (loop name).id_str

let gen_qualid state ctxt name : Ptree.qualid =
  let id = gen_ident state ctxt name in
  mk_qualid [id.id_str]

let add_ident kind ctxt id id' =
  let name = mk_qualid [id'] in
  let ident_map = IdentM.update id (function
      | None -> Some (kind, name)
      | Some (k, n) -> Some (kind, name)
    ) ctxt.ident_map in
  { ctxt with ident_map }

let add_logic_ident = add_ident Id_logic
let add_local_ident ty = add_ident (Id_local ty)

(* -------------------------------------------------------------------------- *)
(* Compiling types                                                            *)
(* -------------------------------------------------------------------------- *)

let rec pty_of_ty (t: ity) : Ptree.pty =
  match t with
  | Tint -> int_type
  | Trgn -> rgn_type
  | Tbool -> bool_type
  | Tunit -> unit_type
  | Tanyclass | Tclass _ -> reference_type
  | Tmath (name, None) ->
    let tyname = mk_qualid [id_name @@ name] in
    PTtyapp (tyname, [])
  | Tmath (Id "array", Some ty) -> (* internal math array type *)
    let base_ty = pty_of_ty ty in
    PTtyapp (mk_qualid ["A"; "array"], [base_ty])
  | Tmath (name, Some ty) ->
    let tyname = mk_qualid [id_name @@ name] in
    PTtyapp (tyname, [pty_of_ty ty])
  | _ -> invalid_arg "pty_of_ty"

let rec default_value ctxt (t: ity) : Ptree.expr =
  match t with
  | Tint -> mk_econst 0
  | Trgn -> mk_qevar @@ empty_rgn
  | Tbool -> mk_expr Efalse
  | Tunit -> mk_expr (Etuple [])
  | Tanyclass | Tclass _ -> null_const
  | Tmath (Id "array", Some ty) -> (* internal math array type *)
    mk_expr (Eidapp (array_make_fn, [mk_econst 0; default_value ctxt ty]))
  | Tmath (name, _) -> mk_abstract_expr [] (pty_of_ty t) empty_spec
  | _ -> invalid_arg "pty_of_ty"

let rec default_value_term ctxt (t: ity) : Ptree.term =
  match t with
  | Tint -> mk_tconst 0
  | Trgn -> mk_qvar @@ empty_rgn
  | Tbool -> mk_term Tfalse
  | Tunit -> mk_term (Ttuple [])
  | Tanyclass | Tclass _ -> null_const_term
  | Tmath (Id "array", Some ty) -> (* internal math array type *)
    array_make_fn <*> [mk_tconst 0; default_value_term ctxt ty]
  | Tmath (name, _) ->
    let default =
      match IdentM.find name ctxt.extty_map with
      | id -> id
      | exception Not_found ->
        failwith ("Unknown default for " ^ string_of_ident name) in
    mk_var % mk_ident @@ id_name default
  | _ -> invalid_arg ("pty_of_ty: " ^ T.string_of_ity t)


(* -------------------------------------------------------------------------- *)
(* State encoding

   type heap = { mutable field_1 : map reference field_1_ty;
                 ...
                 mutable field_n : map reference field_n_ty; }

   type state = { mutable heap : heap;
                 mutable alloct : map reference reftype;
                 ... globals ... }
*)
(* -------------------------------------------------------------------------- *)

let heap_type  : Ptree.pty = PTtyapp (mk_qualid ["heap"], [])
let state_type : Ptree.pty = PTtyapp (mk_qualid ["state"], [])
let refperm_type : Ptree.pty = PTtyapp (mk_qualid ["PreRefperm"; "t"], [])

let st_heap_field = mk_ident "heap"
let st_alloct_field = mk_ident "alloct"

(* st_load ctxt s (y, f) = ``find y s.heap.f'' *)
let st_load ctxt s (y, f) : Ptree.expr =
  let f = simple_resolve_field ctxt f.T.node in
  let m = s %. st_heap_field %. f in
  let y = lookup_id ctxt s y.T.node in
  map_find (mk_qevar m) y

(* We also need a Ptree.term variant of st_load in order to use it in
   formulas and specs *)
let st_load_term ctxt s (y, f) : Ptree.term =
  let f = simple_resolve_field ctxt f.T.node in
  let m = s %. st_heap_field %. f in
  let y = lookup_id_term ctxt s y.T.node in
  map_find_fn <*> [mk_qvar m; y]

(* st_store ctxt s (y, f) e = ``s.heap.f <- add y e s.heap.f'' *)
let st_store ?msg ctxt s (y, f) e : Ptree.expr =
  let y = lookup_id ctxt s y in
  let f = lookup_field ctxt f in
  let field_map = mk_qevar (s %. st_heap_field %. f) in
  let new_map = map_add field_map y e in
  match msg with
  | None   -> mk_expr (Eassign [field_map, None, new_map])
  | Some m -> mk_expr (Eassign [field_map, None, explain_expr new_map m])

(* st_load_old ctxt s (y, f) = ``find y (old s.heap.f)'' *)
let st_load_old ctxt s (y, f) : Ptree.term =
  let y = lookup_id_term ctxt s y in
  let f = lookup_field ctxt f in
  let field_map = mk_qvar (s %. st_heap_field %. f) in
  let field_map = mk_old_term field_map in
  map_find_fn <*> [field_map; y]

(* st_has_type s r k = ``find r s.alloct = (mk_reftype_ctor k)'' *)
let st_has_type s r k : Ptree.term =
  let alloc_type_map = mk_qvar (s %. st_alloct_field) in
  let find_typeof_r  = map_find_fn <*> [alloc_type_map; r] in
  let class_type = ~* (mk_reftype_ctor k) in
  find_typeof_r ==. class_type

(* st_add_type s r k = ``add r (mk_reftype_ctor k) s.alloct'' *)
let st_add_type ctxt s r k : Ptree.term =
  let r = lookup_id_term ctxt s r in
  let alloct_map = mk_qvar (s %. st_alloct_field) in
  let class_type = ~* (mk_reftype_ctor k) in
  map_add_fn <*> [r; class_type; alloct_map]

let st_old_has_type s r k : Ptree.term =
  let alloct_map    = mk_old_term (mk_qvar (s %. st_alloct_field)) in
  let find_typeof_r = map_find_fn <*> [alloct_map; r] in
  let class_type = ~* (mk_reftype_ctor k) in
  find_typeof_r ==. class_type

(* st_previously_unalloc'd = ``not (mem r (old s.alloct))'' *)
let st_previously_unalloc'd s r : Ptree.term =
  let oalloc   = mk_old_term (mk_qvar (s %. st_alloct_field)) in
  let mem_lloc = map_mem_fn <*> [r; oalloc] in
  mk_term (Tnot mem_lloc)

let st_load_array ctxt s a idx =
  let open T in
  match a.ty with
  | Tclass cname when Ctbl.is_array_like_class ctxt.ctbl cname ->
    let slots = match Ctbl.array_like_slots_field ctxt.ctbl cname with
      | None -> assert false
      | Some (slots, ty) -> slots -: ty in
    let value = st_load ctxt s (a, slots) in
    mk_expr (Eidapp (array_get_fn, [value; idx]))
  | _ -> invalid_arg "st_load_array: expected an array-like class"

let st_load_array_term ctxt s a idx =
  let open T in
  match a.ty with
  | Tclass cname when Ctbl.is_array_like_class ctxt.ctbl cname ->
    let slots = match Ctbl.array_like_slots_field ctxt.ctbl cname with
      | None -> assert false
      | Some (slots, ty) -> slots -: ty in
    let value = st_load_term ctxt s (a, slots) in
    array_get_fn <*> [value; idx]
  | _ -> invalid_arg "st_load_array_term: expected an array-like class"

let st_store_array ?msg ctxt s a idx v =
  let open T in
  match a.ty with
  | Tclass cname when Ctbl.is_array_like_class ctxt.ctbl cname ->
    let slots = match Ctbl.array_like_slots_field ctxt.ctbl cname with
      | None -> assert false
      | Some (slots, ty) -> mk_ident (id_name slots) in
    let slots = mk_qevar (s %. st_heap_field %. slots) in
    let aexpr = lookup_id ctxt s a.node in
    let array = mk_expr (Eidapp (map_find_fn, [slots; aexpr])) in
    let upd0  = mk_expr (Eidapp (array_set_fn, [array; idx; v])) in
    let upd1  = map_add slots aexpr upd0 in
    begin match msg with
      | None   -> mk_expr (Eassign [slots, None, upd1])
      | Some m -> mk_expr (Eassign [slots, None, explain_expr upd1 m])
    end
  | _ -> invalid_arg "st_store_array: expected an array-like class"


(* -------------------------------------------------------------------------- *)
(* Image functions

   For each field f with DeclClass(f) = k we generate a function
   image_k_f with type state -> rgn -> rgn.
*)
(* -------------------------------------------------------------------------- *)

let mk_image_fn_ident (fname: Ptree.ident) : Ptree.ident =
  mk_ident ("img_" ^ fname.id_str)

let mk_image_fn_qualid fname : Ptree.qualid =
  qualid_of_ident @@ mk_image_fn_ident fname

let mk_image_fn fname : Ptree.decl =
  let image_fn_name = mk_image_fn_ident fname in
  let image_fn_ty : Ptree.pty =
    PTarrow (state_type, PTarrow (rgn_type, rgn_type)) in
  let image_fn = mk_ldecl image_fn_name [] image_fn_ty None in
  Dlogic [image_fn]

let mk_image_axiom_name f : Ptree.ident =
  let img_fn = mk_image_fn_ident f in
  mk_ident @@ img_fn.id_str ^ "_ax"

let rec mk_image_axiom ctxt decl_class f (fty: ity) : Ptree.decl =
  match fty with
  | Trgn | Tclass _ -> mk_image_axiom_aux ctxt decl_class f fty
  | _ ->
    let term =
      let+! state, _ = bindvar (~. (fresh_name ctxt "s"), state_type) in
      let+! rgn, _ = bindvar (~. (fresh_name ctxt "r"), rgn_type) in
      let img_fn_ap = (mk_image_fn_qualid f) <*> [~* state; ~* rgn] in
      return (img_fn_ap ==. (mk_qvar empty_rgn)) in
    Dprop(Decl.Paxiom, mk_image_axiom_name f, build_term term)

and mk_image_axiom_aux ctxt decl_class f (fty: ity) : Ptree.decl =
  let mk_axiom term = Ptree.Dprop (Decl.Paxiom, mk_image_axiom_name f, term) in
  let img_fn_symb = mk_image_fn_qualid f in
  let term =
    let+! state, _ = bindvar (~. (fresh_name ctxt "s"), state_type) in
    let+! rgn, _   = bindvar (~. (fresh_name ctxt "r"), rgn_type) in
    let+! p, _     = bindvar (~. (fresh_name ctxt "p"), reference_type) in
    let pmem_img = mem_fn <*> [~* p; img_fn_symb <*> [~* state; ~* rgn]] in
    let inner_term =
      let+? q, _ = bindvar (~. (fresh_name ctxt "q"), reference_type) in
      let state_qid = qualid_of_ident state in
      let qalloc = map_mem_fn <*> [~* q; mk_qvar(state_qid%.st_alloct_field)] in
      let qty = map_find_fn <*> [mk_qvar(state_qid%.st_alloct_field); ~* q] in
      let qty = qty ==. (~* (mk_reftype_ctor decl_class)) in
      let qmem = mem_fn <*> [~* q; ~* rgn] in
      let qval = map_find_fn <*> [mk_qvar(state_qid%.st_heap_field%.f); ~* q] in
      let pqrel =
        match fty with
        | Trgn -> mem_fn <*> [~* p; qval]
        | Tclass _ -> ~* p ==. qval
        | _ -> invalid_arg "mk_image_axiom_aux" in
      return (qalloc ^&& (qty ^&& (qmem ^&& pqrel))) in
    return (pmem_img <==> (build_term inner_term)) in
  mk_axiom (build_term term)


(* -------------------------------------------------------------------------- *)
(* Building the State module                                                  *)
(* -------------------------------------------------------------------------- *)

(* NOTE: the ``Reference'' theory is part of the standard library. *)
(* Possible signature: mk: penv -> Ptree.mlw_file *)
module Build_State = struct
  open T

  let state_module_name = mk_ident "State"

  let mk_field name ty mut gho : Ptree.field =
    { f_loc = Loc.dummy_position;
      f_ident = name;
      f_pty = ty;
      f_mutable = mut;
      f_ghost = gho }

  let mk_mutable_field name ty gho : Ptree.field = mk_field name ty true gho

  (* Maps from references to pty *)
  let mk_map_type pty : Ptree.pty =
    PTtyapp (mk_qualid ["M"; "t"], [pty])

  let mut_field_of_field_decl ctbl {field_name; field_ty; attribute} =
    let gho = Ctbl.is_ghost_field ctbl field_name.node in
    let field_name = mk_ident @@ id_name field_name.node in
    let field_type = mk_map_type @@ pty_of_ty field_ty in
    mk_mutable_field field_name field_type gho

  let mk_heap_type ctxt : Ptree.type_def =
    let flds = Ctbl.known_fields ctxt.ctbl in
    let flds = map (mut_field_of_field_decl ctxt.ctbl) flds in
    TDrecord flds

  let mk_heap_decl ctxt : Ptree.decl =
    let def = mk_heap_type ctxt in
    let decl = Ptree.{
        td_loc = Loc.dummy_position;
        td_ident = mk_ident "heap";
        td_params = [];
        td_vis = Public;
        td_mut = false;
        td_inv = [];
        td_wit = [];
        td_def = def } in
    Dtype [decl]

  let mk_reftype ctbl : Ptree.type_def =
    let mk_ctor name = (Loc.dummy_position, name, []) in
    let class_names = Ctbl.known_class_names ctbl in
    let ctors = map mk_reftype_ctor class_names in
    TDalgebraic (map mk_ctor (ctors))

  let mk_reftype_decl ctbl : Ptree.decl =
    let reftype = mk_reftype ctbl in
    let decl = Ptree.{
        td_loc = Loc.dummy_position;
        td_ident = mk_ident "reftype";
        td_params = [];
        td_vis = Public;
        td_mut = false;
        td_inv = [];
        td_wit = [];
        td_def = reftype } in
    Dtype [decl]

  let extern_types_in_penv penv : (ident * ident) list =
    let exttys = ref [] in
    let open IdentM in
    let rec walk_intr = function
      | [] -> ()
      | Intr_extern (Extern_type (ty, def)) :: rest ->
        exttys := (ty, def) :: !exttys;
        walk_intr rest
      | _ :: rest -> walk_intr rest in
    let rec walk_mdl = function
      | [] -> ()
      | Mdl_extern (Extern_type (ty, def)) :: rest ->
        exttys := (ty, def) :: !exttys;
        walk_mdl rest
      | _ :: rest -> walk_mdl rest in
    let rec walk_bimdl = function
      | [] -> ()
      | Bimdl_extern (Extern_type (ty, def)) :: rest ->
        exttys := (ty, def) :: !exttys;
        walk_bimdl rest
      | _ :: rest -> walk_bimdl rest in
    IdentM.iter (fun name p ->
        match p with
        | Unary_interface idef -> walk_intr idef.intr_elts
        | Unary_module mdef -> walk_mdl mdef.mdl_elts
        | Relation_module bmdef -> walk_bimdl bmdef.bimdl_elts
      ) penv;
    !exttys

  let globals_in_penv penv : (modifier * ident * ity) list =
    let globals = ref [] in
    let rec walk_intr = function
      | [] -> ()
      | Intr_vdecl (m, id, ty) :: rest ->
        globals := (m, id.node, ty) :: !globals;
        walk_intr rest
      | _ :: rest -> walk_intr rest in
    IdentM.iter (fun name p ->
        match p with
        | Unary_interface idef -> walk_intr idef.intr_elts
        | _ -> ()
      ) penv;
    !globals

  (* fields_of_globals C P = fs

     fs is a list of additional fields the state type must have in
     order to encode globals.
  *)
  let fields_of_globals ctbl globals : Ptree.field list =
    map (fun (modif, id, ty) ->
        let id_name = mk_ident @@ id_name id in
        let pty = pty_of_ty ty in
        let gho = match modif with Ghost -> true | _ -> ty = Trgn in
        mk_mutable_field id_name pty gho
      ) globals

  let rec state_decl ctxt globals : Ptree.decl =
    let reftype = Ptree.PTtyapp(mk_qualid["reftype"],[]) in
    let fields =
      [ mk_mutable_field st_heap_field (PTtyapp(mk_qualid["heap"],[])) false;
        mk_mutable_field st_alloct_field (mk_map_type reftype) true ]
      @ globals in
    let def = Ptree.TDrecord fields in
    let decl = Ptree.{
        td_loc = Loc.dummy_position;
        td_ident = mk_ident "state";
        td_params = [];
        td_vis = Public;
        td_mut = false;
        td_inv = mk_ok_state ctxt globals;
        td_wit = mk_ok_state_witness globals;
        td_def = def } in
    Dtype [decl]

  and mk_ok_state_witness globals : (Ptree.qualid * Ptree.expr) list =
    let empty_spec = mk_spec [] [] [] [] in
    let mk_wit Ptree.{f_ident; f_pty; _} =
      let f_val =
        if f_pty = rgn_type
        then mk_qevar empty_rgn
        else mk_abstract_expr [] f_pty empty_spec in
      qualid_of_ident f_ident, f_val in
    let globals_wit = map mk_wit globals in
    [qualid_of_ident st_heap_field, mk_abstract_expr [] heap_type empty_spec;
     qualid_of_ident st_alloct_field, map_empty_expr;
    ] @ globals_wit

  and mk_ok_state ctxt globals : Ptree.term list =
    let classes = Ctbl.known_classes ctxt.ctbl in
    let alloct_map = mk_var st_alloct_field in
    let null_not_in_alloc =
      let inner = map_mem_fn <*> [null_const_term; alloct_map] in
      mk_term (Tnot inner) in
    let mk_ok_state_class_cond c =
      let inner =
        let+! p,_ = bindvar (~. (fresh_name ctxt "p"), reference_type) in
        let p_alloc'd = map_mem_fn <*> [~*p; alloct_map] in
        let body = mk_ok_state_class ctxt (~*p) c in
        return (p_alloc'd ^==> body) in
      build_term inner in
    let class_conds = map mk_ok_state_class_cond classes in
    let global_conds = concat_map (mk_ok_state_global_cond ctxt) globals in
    null_not_in_alloc :: class_conds @ global_conds

  (* If f is a global of type rgn, then return a singleton list containing:

       forall q:reference. mem q f -> q = null \/ mem q s.alloct

     otherwise, return the empty list.
  *)
  and mk_ok_state_global_cond ctxt {f_ident; f_pty; _} =
    if not (f_pty = rgn_type) then [] else
      [build_term begin
          let state = mk_qualid ["dummy"] in
          let+! q, _ = bindvar (gen_ident state ctxt "q", reference_type) in
          let qmem = mem_fn <*> [~*q; mk_var f_ident] in
          let q_eq_null = (~*q) ==. null_const_term in
          let q_mem_alloc = map_mem_fn <*> [~*q; mk_var st_alloct_field] in
          return (qmem ^==> (q_eq_null ^|| q_mem_alloc))
        end]

  and mk_ok_state_classes ctxt p cdecls = (* FIXME: UNUSED *)
    assert (length cdecls >= 1);
    match cdecls with
    | [] -> assert false
    | [c] -> mk_ok_state_class ctxt p c
    | c::cs -> mk_ok_state_class ctxt p c ^&& mk_ok_state_classes ctxt p cs

  (* okState for a single class *)
  and mk_ok_state_class ctxt p cdecl =
    let open List in
    let resolve_field f =
      let f' = f.field_name.node in
      (* FIXME: do we really need field_map anymore? *)
      match IdentM.find f' ctxt.field_map with
      | fld -> (fld, f.field_ty)
      | exception Not_found -> (~. (id_name f'), f.field_ty) in
    let flds = map resolve_field cdecl.fields in
    let kflds = filter (fun (_,p) -> is_class_ty p) flds in
    let rflds = filter (fun (_,p) -> p = Trgn) flds in
    let kconds = map (uncurry (mk_ok_state_classfield_cond p)) kflds in
    let rconds = map (uncurry (mk_ok_state_rgnfield_cond ctxt p)) rflds in
    let has_flds = mk_ok_state_has_fields p (map fst flds) in
    let conds = kconds @ rconds in
    let inner =
      if length conds >= 1
      then has_flds ^&& mk_conjs conds
      else has_flds in
    let inner =
      if Ctbl.is_array_like_class ctxt.ctbl cdecl.class_name
      then inner ^&& mk_ok_state_array_cond ctxt p cdecl.class_name
      else inner in
    let p_has_type_k =
      let alloc_map = mk_var st_alloct_field in
      let type_of_p = map_find_fn <*> [alloc_map; p] in
      let class_typ = mk_var (mk_reftype_ctor cdecl.class_name) in
      type_of_p ==. class_typ in
    p_has_type_k ^==> inner

  (* /\f:flds, mem p s.heap.f *)
  and mk_ok_state_has_fields p flds : Ptree.term =
    let has_field f =
      let heap_fld  = qualid_of_ident st_heap_field in
      let field_map = mk_qvar (heap_fld %. f) in
      map_mem_fn <*> [p; field_map] in
    match flds with
    | [] -> invalid_arg "mk_ok_state_has_fields: empty field list"
    | _  -> mk_conjs (map has_field flds)

  (* find p s.heap.XLength = length(find p s.heap.XSlots) *)
  and mk_ok_state_array_cond ctxt p k : Ptree.term =
    assert (Ctbl.is_array_like_class ctxt.ctbl k);
    let length = fst (Opt.get (Ctbl.array_like_length_field ctxt.ctbl k)) in
    let length = mk_ident (id_name length) in
    let slots = fst (Opt.get (Ctbl.array_like_slots_field ctxt.ctbl k)) in
    let slots = mk_ident (id_name slots) in
    let heap_field = qualid_of_ident st_heap_field in
    let len_val = map_find_fn <*> [mk_qvar (heap_field %. length); p] in
    let arr_val = map_find_fn <*> [mk_qvar (heap_field %. slots); p] in
    let inner_len  = array_len_fn <*> [arr_val] in
    let class_cond = mk_ok_state_array_class_cond ctxt p k in
    let length_gt0 = mk_term (Tinfix (len_val, mk_infix ">=", mk_tconst 0)) in
    mk_conjs (length_gt0 :: (len_val ==. inner_len) :: class_cond)

  and mk_ok_state_array_class_cond ctxt p k : Ptree.term list =
    assert (Ctbl.is_array_like_class ctxt.ctbl k);
    let base_ty = Opt.get (Ctbl.element_type ctxt.ctbl k) in
    match base_ty with
    | Tclass cls ->
      let state = mk_qualid ["dummy"] in (* UNUSED in generated formula *)
      let arr_id = gen_ident state ctxt "arr" in
      let slots = fst (Opt.get (Ctbl.array_like_slots_field ctxt.ctbl k)) in
      let slots = mk_ident (id_name slots) in
      let heap_field = qualid_of_ident st_heap_field in
      let arr_val = map_find_fn <*> [mk_qvar (heap_field %. slots); p] in
      let alloct = mk_var st_alloct_field in
      let inner_term = build_term begin
          let+! i, _ = bindvar (gen_ident state ctxt "i", int_type) in
          let arr_len = array_len_fn <*> [~*arr_id] in
          let i_ge_0 = mk_term (Tinfix (mk_tconst 0, mk_infix "<=", ~*i)) in
          let i_lt_len = mk_term (Tinfix (~*i, mk_infix "<", arr_len)) in
          let cell_id = gen_ident state ctxt "v" in
          let cell_val = array_get_fn <*> [~*arr_id; ~*i] in
          let cell_null = (~*cell_id) ==. null_const_term in
          let cell_alloc'd = map_mem_fn <*> [~*cell_id; alloct] in
          let cell_typ = map_find_fn <*> [alloct; ~*cell_id] in
          let cell_typ_eq = cell_typ ==. (mk_var (mk_reftype_ctor cls)) in
          let cond = cell_null ^|| (cell_alloc'd ^&& cell_typ_eq) in
          let bind_cell_term = mk_term (Tlet (cell_id, cell_val, cond)) in
          return (i_ge_0 ^==> i_lt_len ^==> bind_cell_term)
        end in
      [mk_term (Tlet (arr_id, arr_val, inner_term))]
    | _ -> []

  (* find p s.heap.fld = null \/ find (find p s.heap.fld) s.alloct = K *)
  and mk_ok_state_classfield_cond p fld fld_ty : Ptree.term =
    assert (is_class_ty fld_ty);
    let cls = match fld_ty with Tclass cname -> cname | _ -> assert false in
    let field_map = mk_qvar ((qualid_of_ident st_heap_field) %. fld) in
    let field_val = map_find_fn <*> [field_map; p] in
    let fval_null = field_val ==. null_const_term in
    let cls_rtype = mk_var (mk_reftype_ctor cls) in
    let alloc_map = mk_var st_alloct_field in
    let alloc'd   = map_mem_fn <*> [field_val; alloc_map] in
    let fval_type = (map_find_fn <*> [alloc_map; field_val]) ==. cls_rtype in
    fval_null ^|| (alloc'd ^&& fval_type)

  (* For fld of type rgn, emit:

     forall q:reference. mem q s.heap.fld[p] -> q = null \/ mem q s.alloct
  *)
  and mk_ok_state_rgnfield_cond ctxt p fld fld_ty : Ptree.term =
    assert (fld_ty = Trgn);
    build_term begin
      let st_name = mk_qualid ["dummy"] in
      let+! q, _ = bindvar (gen_ident st_name ctxt "q", reference_type) in
      let field_map = mk_qvar ((qualid_of_ident st_heap_field) %. fld) in
      let field_val = map_find_fn <*> [field_map; p] in
      let qmem = mem_fn <*> [~*q; field_val] in
      let q_eq_null = (~*q) ==. null_const_term in
      let q_mem_alloc = map_mem_fn <*> [~*q; mk_var st_alloct_field] in
      return (qmem ^==> (q_eq_null ^|| q_mem_alloc))
    end

  let has_class_type_pred cname =
    let cname = mk_ident (id_name cname) in
    mk_qualid ["has" ^ String.capitalize_ascii cname.id_str ^ "Type"]

  (* For each class K in the ctbl, generate a predicate which asserts
     that a reference has a given class type. *)
  let rec mk_has_class_type_predicates ctxt : Ptree.decl list =
    let state_id = fresh_name ctxt "s" in
    let state = mk_qualid [state_id] in
    let p_id = gen_ident state ctxt "p" in
    let classes = Ctbl.known_classes ctxt.ctbl in
    let predicates =
      let f ({class_name;_} as c) =
        (class_name, mk_has_class_type_class ctxt state (~* p_id) c) in
      map f classes in
    let predicates =
      map (fun (name, term) ->
          let pred_name = has_class_type_pred name in
          let state_param = mk_param (mk_ident state_id) false state_type in
          let p_param = mk_param p_id false reference_type in
          let inner = Ptree.{
              ld_loc = Loc.dummy_position;
              ld_ident = ident_of_qualid pred_name;
              ld_params = [state_param; p_param];
              ld_type = None;
              ld_def = Some term } in
          Ptree.Dlogic [inner]
        ) predicates in
    predicates

  and mk_has_class_type_class ctxt state p cdecl =
    let alloc_map = mk_qvar (state %. st_alloct_field) in
    let p_is_null = p ==. null_const_term in
    let p_alloc'd = map_mem_fn <*> [p; alloc_map] in
    let p_typ = map_find_fn <*> [alloc_map; p] in
    let p_class_typ = p_typ ==. (~* (mk_reftype_ctor cdecl.class_name)) in
    p_is_null ^|| (p_alloc'd ^&& p_class_typ)

  (* FIXME: almost identical to mk_ok_state_classfield_cond *)
  (* DEPRECATED: TO BE REMOVED *)
  and mk_has_class_type_classfield_cond p state fld fld_ty : Ptree.term =
    assert (is_class_ty fld_ty);
    let cls = match fld_ty with Tclass cname -> cname | _ -> assert false in
    let field_map = mk_qvar (state %. st_heap_field %. fld) in
    let field_val = map_find_fn <*> [field_map; p] in
    let fval_null = field_val ==. null_const_term in
    let cls_rtype = mk_var (mk_reftype_ctor cls) in
    let alloc_map = mk_qvar (state %. st_alloct_field) in
    let alloc'd   = map_mem_fn <*> [field_val; alloc_map] in
    let fval_type = map_find_fn <*> [alloc_map; field_val] in
    let fval_type = fval_type ==. cls_rtype in
    fval_null ^|| (alloc'd ^&& fval_type)

  let is_allocated_pred = mk_qualid ["isAllocated"]

  let is_allocated_predicate : Ptree.decl =
    let state_id = mk_ident "s" in (* FIXME: use gen_ident instead? *)
    let state = qualid_of_ident state_id in
    let state_param = mk_param state_id false state_type in
    let p_id = mk_ident "p" in  (* FIXME: use gen_ident instead? *)
    let p_param = mk_param p_id false reference_type in
    let body = map_mem_fn <*> [~* p_id; mk_qvar (state %. st_alloct_field)] in
    let ldecl =
      Ptree.{ ld_loc = Loc.dummy_position;
              ld_ident = ident_of_qualid is_allocated_pred;
              ld_params = [state_param; p_param];
              ld_type = None;
              ld_def = Some body } in
    Dlogic [ldecl]

  let is_valid_rgn_pred = mk_qualid ["isValidRgn"]

  (* is_valid_rgn_predicate (s: state) (r: rgn) =
     forall q:reference. mem q r -> q = null \/ mem q s.alloct *)
  let is_valid_rgn_predicate : Ptree.decl =
    (* TODO: check if any name clashes can occur. *)
    let state_id = mk_ident "s" in
    let state = qualid_of_ident state_id in
    let st_alloct = mk_qvar (state %. st_alloct_field) in
    let state_param = mk_param state_id false state_type in
    let rgn_id = mk_ident "r" in
    let rgn_param = mk_param rgn_id false rgn_type in
    let body = build_term begin
        let+! q, _ = bindvar (mk_ident "q", reference_type) in
        let qmem = mem_fn <*> [~*q; ~*rgn_id] in
        let q_eq_null = (~*q) ==. null_const_term in
        let q_mem_alloc = map_mem_fn <*> [~*q; st_alloct] in
        return (qmem ^==> (q_eq_null ^|| q_mem_alloc))
      end in
    let ldecl =
      Ptree.{ ld_loc = Loc.dummy_position;
              ld_ident = ident_of_qualid is_valid_rgn_pred;
              ld_params = [state_param; rgn_param];
              ld_type = None;
              ld_def = Some body } in
    Dlogic [ldecl]

  let typeof_rgn_predicate : Ptree.decl =
    (* FIXME: use gen_ident instead of mk_ident? Need the ctxt though *)
    let reftype = Ptree.PTtyapp(mk_qualid ["reftype"],[]) in
    let name = ident_of_qualid typeof_rgn_fn in
    let state_id = mk_ident "s" in
    let state = qualid_of_ident state_id in
    let state_param = mk_param state_id false state_type in
    let typ_id = mk_ident "t" in
    let typ_param = mk_param typ_id false reftype in
    let rgn_id = mk_ident "r" in
    let rgn_param = mk_param rgn_id false rgn_type in
    let body =
      let+! p, _   = bindvar (mk_ident "p", reference_type) in
      let pmemrgn  = mem_fn <*> [~*p; ~*rgn_id] in
      let pnull    = (~*p) ==. null_const_term in
      let palloc'd = map_mem_fn <*> [~*p; mk_qvar(state %.st_alloct_field)] in
      let ptyp     = map_find_fn <*> [mk_qvar(state %.st_alloct_field); ~*p] in
      let ptyp_eq  = ptyp ==. (~*typ_id) in
      return (pmemrgn ^==> (pnull ^|| (palloc'd ^&& ptyp_eq))) in
    let inner = build_term body in
    let ldecl = Ptree.{
        ld_loc = Loc.dummy_position;
        ld_ident = name;
        ld_params = [state_param; rgn_param; typ_param];
        ld_type = None;
        ld_def = Some inner } in
    Dlogic [ldecl]

  (* mk_new_classes G CT = ms

     ms is a list of Why3 functions.  For each class K in CT, there is
     a function called "mk_K" in ms.  Each such function has the
     following spec:

     val mk_K (s: state) : reference
       ensures  { find result (old s).alloct = Unalloc }
       ensures  { s.alloct = add result K (old s).alloct }
       ensures  { "fields of object result points to have 0-equivalent values" }
       ensures  { "no existing object of the same type has a field
                   that points to result" }
       writes   { s.alloct, "all fields of result" }
  *)
  let rec mk_new_classes ctxt ctbl : ctxt * Ptree.decl list =
    let classes = Ctbl.known_class_names ctbl in
    List.fold_right (fun cname (ctxt, decls) ->
        let name = mk_alloc_name cname in
        let decl = mk_new_class ctxt ctbl cname name in
        (* FIXME: Here, we associate each ctor method K with mk_K.
           However, it should be associated with init_K.
           Check whether it is indeed proper to remove the below statement. *)
        (* let ctxt = add_ident Id_other ctxt cname name.id_str in *)
        (ctxt, decl :: decls)
      ) classes (ctxt, [])

  and mk_new_class ctxt ctbl cname mkname : Ptree.decl =
    let open List in
    let zero_equiv_value ctxt state fname : Ptree.term * Ptree.post list =
      let ty = Ctbl.field_type ctbl ~field:fname in
      match ty with
      | None -> invalid_arg "zero_equiv_value"
      | Some ty ->
        let result_term = mk_var (mk_ident "result") in
        let value = default_value_term ctxt ty in
        let fld = lookup_field ctxt fname in
        let wrttn_fld = mk_qvar (state%.st_heap_field%.fld) in
        let old_fld = mk_old_term wrttn_fld in
        let add_to_ofld = map_add_fn <*> [result_term; value; old_fld] in
        let equiv_flds = wrttn_fld ==. add_to_ofld in
        wrttn_fld, [mk_ensures equiv_flds] in
    let cname_ctor = mk_reftype_ctor cname in
    let field_names = Ctbl.field_names ctbl cname in
    let state_ident = ~. (fresh_name ctxt "s") in
    let state = qualid_of_ident state_ident in
    let state_param = mk_param state_ident false state_type in
    let result = mk_ident "result" in
    let result_term = mk_var result in
    let ctxt = add_ident Id_other ctxt (Id "result") "result" in
    let st_alloc_type = mk_qvar (state %. st_alloct_field) in
    let ost_alloc_type = mk_old_term st_alloc_type in
    let add_args = [result_term; mk_var cname_ctor; ost_alloc_type] in
    let add_to_st_alloc_type = map_add_fn <*> add_args in
    (* Postconditions and writes *)
    let unalloc'd_post =
      mk_ensures (st_previously_unalloc'd state result_term) in
    let alloc_type_post = mk_ensures (st_alloc_type ==. add_to_st_alloc_type) in
    let result_non_null_post = mk_ensures (result_term =/=. null_const_term) in
    let has_ctype_post =
      let ctype_pred = has_class_type_pred cname in
      mk_ensures (ctype_pred <*> [mk_qvar state; result_term]) in
    let others_unchanged_post = mk_ensures @@ build_term begin
        let+! p, _ = bindvar (gen_ident state ctxt "p", reference_type) in
        let palloc'd = map_mem_fn <*> [~*p; ost_alloc_type] in
        let pmemalloc = map_mem_fn <*> [~*p; st_alloc_type] in
        let p_otype = map_find_fn <*> [ost_alloc_type; ~*p] in
        let p_type = map_find_fn <*> [st_alloc_type; ~*p] in
        let ty_unchanged = p_otype ==. p_type in
        return (palloc'd ^==> (pmemalloc ^&& ty_unchanged))
      end in
    let ze_posts = map (zero_equiv_value ctxt state) field_names in
    let ze_writes, ze_posts = split ze_posts in
    let postconditions = [
      unalloc'd_post;
      alloc_type_post;
      others_unchanged_post;
      result_non_null_post;
      has_ctype_post;
    ] @ flat ze_posts in
    let writes = mk_qvar @@ Qdot(state, st_alloct_field) in
    let spec = mk_spec_simple [] postconditions (writes :: ze_writes) in
    let params = [state_param] in
    let absfun = mk_abstract_expr params reference_type spec in
    Dlet (mkname, false, Expr.RKnone, absfun)


  (* ------------------------------------------------------------------------ *)
  (* The okRefperm predicate                                                  *)
  (* ------------------------------------------------------------------------ *)

  let ok_refperm_predicate = mk_qualid ["okRefperm"]

  let ok_refperm_decl : Ptree.decl =
    let lstate_id = mk_ident "sl" and rstate_id = mk_ident "sr" in
    let refperm_id = mk_ident "pi" in
    let lstate, rstate = map_pair qualid_of_ident (lstate_id, rstate_id) in
    let refperm = qualid_of_ident refperm_id in

    let lor_map = mk_qvar (refperm %. mk_ident "lor") in
    let rol_map = mk_qvar (refperm %. mk_ident "rol") in
    let lalloc  = mk_qvar (lstate %. st_alloct_field) in
    let ralloc  = mk_qvar (rstate %. st_alloct_field) in

    let lstate_alloc_cond =
      build_term begin
        let+! p,_ = bindvar (mk_ident "p", reference_type) in
        let p_in_lor = map_mem_fn <*> [~*p; lor_map] in
        let p_in_alloc = map_mem_fn <*> [~*p; lalloc] in
        return (p_in_lor ^==> p_in_alloc)
      end in

    let rstate_alloc_cond =
      build_term begin
        let+! q,_ = bindvar (mk_ident "q", reference_type) in
        let q_in_rol = map_mem_fn <*> [~*q; rol_map] in
        let q_in_alloc = map_mem_fn <*> [~*q; ralloc] in
        return (q_in_rol ^==> q_in_alloc)
      end in

    let type_resp_cond =
      build_term begin
        let+! p,_ = bindvar (mk_ident "p", reference_type) in
        let+! q,_ = bindvar (mk_ident "q", reference_type) in
        let p_in_lor = map_mem_fn <*> [~*p; lor_map] in
        let p_image = map_find_fn <*> [lor_map; ~*p] in
        let p_image_is_q = p_image ==. (~*q) in
        let p_type = map_find_fn <*> [lalloc; ~*p] in
        let q_type = map_find_fn <*> [ralloc; ~*q] in
        let eq_type = p_type ==. q_type in
        return (p_in_lor ^==> p_image_is_q ^==> eq_type)
      end in

    let body = lstate_alloc_cond ^&& rstate_alloc_cond ^&& type_resp_cond in

    let lstate_param = mk_param lstate_id false state_type in
    let rstate_param = mk_param rstate_id false state_type in
    let refperm_param = mk_param refperm_id false refperm_type in

    let ldecl = Ptree.{
        ld_loc = Loc.dummy_position;
        ld_ident = ident_of_qualid ok_refperm_predicate;
        ld_params = [lstate_param; rstate_param; refperm_param];
        ld_type = None;
        ld_def = Some body } in
    Dlogic [ldecl]

  let ok_refperm sl sr pi =
    ok_refperm_predicate <*> [mk_qvar sl; mk_qvar sr; mk_qvar pi]


  (* ------------------------------------------------------------------------ *)
  (* Utility predicates to make specs easier to read/understand               *)
  (* ------------------------------------------------------------------------ *)

  let alloc_does_not_shrink : Ptree.ident = mk_ident "alloc_does_not_shrink"

  let mk_alloc_does_not_shrink_predicate ctxt : Ptree.decl =
    let spre_id = fresh_name ctxt "pre" in
    let spost_id = fresh_name ctxt "post" in
    let spre,spost = map_pair mk_qualid ([spre_id],[spost_id]) in
    let spre_param = mk_param (mk_ident spre_id) false state_type in
    let spost_param = mk_param (mk_ident spost_id) false state_type in
    let prealloc = mk_qvar (spre %. st_alloct_field) in
    let postalloc = mk_qvar (spost %. st_alloct_field) in
    let inner_term = build_term begin
        let+! p, _ = bindvar (gen_ident spre ctxt "p",reference_type) in
        let p_alloc'd = map_mem_fn <*> [~*p; prealloc] in
        let p_remains_alloc'd = map_mem_fn <*> [~*p; postalloc] in
        let p_has_same_type =
          let type_in_pre = map_find_fn <*> [prealloc; ~*p] in
          let type_in_post = map_find_fn <*> [postalloc; ~*p] in
          type_in_pre ==. type_in_post in
        return (p_alloc'd ^==> (p_remains_alloc'd ^&& p_has_same_type))
      end in
    let ldecl = Ptree.{
        ld_loc = Loc.dummy_position;
        ld_ident = alloc_does_not_shrink;
        ld_params = [spre_param; spost_param];
        ld_type = None;
        ld_def = Some inner_term
      } in
    Dlogic [ldecl]

  let mk_utility_predicates ctxt : Ptree.decl list =
    [mk_alloc_does_not_shrink_predicate ctxt]


  (* ------------------------------------------------------------------------ *)
  (* Agreement predicates                                                     *)
  (* ------------------------------------------------------------------------ *)

  let agreement_predicate_id (fname: Ptree.ident) =
    mk_ident ("agree_" ^ fname.id_str)

  let agreement_on_any : Ptree.ident = mk_ident ("agree_allfields")

  let agreement fname = qualid_of_ident (agreement_predicate_id fname)

  let mk_agreement_predicate ctxt decl_class fname fty : Ptree.decl =
    let lstate_id, rstate_id = mk_ident "sl", mk_ident "sr" in
    let refperm_id, rgn_id = mk_ident "pi", mk_ident "w" in
    let lstate = qualid_of_ident lstate_id in
    let rstate = qualid_of_ident rstate_id in
    let refperm = qualid_of_ident refperm_id in
    let refperm_lor = mk_qvar (refperm %. mk_ident "lor") in
    let rgn = qualid_of_ident rgn_id in
    let ok_refperm = ok_refperm lstate rstate refperm in
    let body =
      let+! o,_ = bindvar (mk_ident "o", reference_type) in
      let o_alloc'd = is_allocated_pred <*> [mk_qvar lstate; ~*o] in
      let o_typ = has_class_type_pred decl_class <*> [mk_qvar lstate; ~*o] in
      let o_in_rgn = mem_fn <*> [~*o; mk_qvar rgn] in
      let o_in_refperm = map_mem_fn <*> [~*o; refperm_lor] in
      let o_img = map_find_fn <*> [refperm_lor; ~*o] in
      let lfmap = mk_qvar (lstate %. st_heap_field %. fname) in
      let rfmap = mk_qvar (rstate %. st_heap_field %. fname) in
      let o_val = map_find_fn <*> [lfmap; ~*o] in
      let o'_val = map_find_fn <*> [rfmap; o_img] in
      let eq = match fty with
        | Tclass _ | Tanyclass -> id_ref_fn <*> [mk_qvar refperm; o_val; o'_val]
        | Trgn -> id_rgn_fn <*> [mk_qvar refperm; o_val; o'_val]
        | _ -> o_val ==. o'_val in
      let eq = explain_term eq "sl(o) ~ sr(pi(o))" in
      return (o_alloc'd ^==> o_typ ^==> o_in_rgn ^==> (o_in_refperm ^&& eq)) in
    let body = ok_refperm ^&& build_term body in
    let lstate_param = mk_param lstate_id false state_type in
    let rstate_param = mk_param rstate_id false state_type in
    let refperm_param = mk_param refperm_id false refperm_type in
    let rgn_param = mk_param rgn_id false rgn_type in
    let params = [lstate_param; rstate_param; refperm_param; rgn_param] in
    let ldecl = Ptree.{
        ld_loc = Loc.dummy_position;
        ld_ident = agreement_predicate_id fname;
        ld_params = params;
        ld_type = None;
        ld_def = Some body } in
    Dlogic [ldecl]

  let mk_agreement_on_any_predicate ctxt : Ptree.decl =
    let known_fields = Ctbl.known_field_names ctxt.ctbl in
    let lstate_id,rstate_id = mk_ident "sl",mk_ident "sr" in
    let refperm_id,rgn_id = mk_ident "pi",mk_ident "w" in
    let inner = foldr (fun f rest ->
        let f = IdentM.find f ctxt.field_map in
        let args = map mk_var [lstate_id; rstate_id; refperm_id; rgn_id] in
        (agreement f <*> args) :: rest
      ) [] known_fields in
    let body = match inner with
      | [] -> None
      | _ -> Some (mk_conjs inner) in
    let lstate_param = mk_param lstate_id false state_type in
    let rstate_param = mk_param rstate_id false state_type in
    let refperm_param = mk_param refperm_id false refperm_type in
    let rgn_param = mk_param rgn_id false rgn_type in
    let params = [lstate_param; rstate_param; refperm_param; rgn_param] in
    let ldecl = Ptree.{
        ld_loc = Loc.dummy_position;
        ld_ident = agreement_on_any;
        ld_params = params;
        ld_type = None;
        ld_def = body;
      } in
    Dlogic [ldecl]

  let mk_agreement_predicates ctxt =
    let ctbl = ctxt.ctbl in
    IdentM.fold (fun f f' decls ->
        let decl_class = match Ctbl.decl_class ctbl f with
          | Some cname -> cname
          | _ -> assert false in
        match Ctbl.field_type ctbl f with
        | Some ty ->
          let agree_pred = mk_agreement_predicate ctxt decl_class f' ty in
          agree_pred :: decls
        | None -> decls
      ) ctxt.field_map [] @ [mk_agreement_on_any_predicate ctxt]


  (* ------------------------------------------------------------------------ *)
  (* Driver                                                                   *)
  (* ------------------------------------------------------------------------ *)

  (* mk P = (ctxt, mdl)

     ctxt contains the global class table and names (possibly mangled)
     of all globals in programs in P.  Additionally, ctxt.field_map is
     populated with all known fields.  mdl is the Why3 state module.
  *)
  let mk penv : ctxt * Ptree.mlw_file =
    let ctbl = Ctbl.of_penv penv in
    let globals = globals_in_penv penv in
    let ctxt = List.fold_right (fun (m, id, ty) ctxt ->
        let name = id_name id in
        add_ident Id_global ctxt id name
      ) globals ini_ctxt in
    let globals = fields_of_globals ctbl globals in
    let fields = Ctbl.known_field_names ctbl in
    let field_map = List.fold_right (fun fld map ->
        IdentM.add fld (mk_ident @@ id_name fld) map
      ) fields IdentM.empty in
    let ctxt = {ctxt with ctbl; field_map} in
    let exttys = extern_types_in_penv penv in
    let ctxt = {ctxt with extty_map = IdentM.of_seq (List.to_seq exttys)} in
    let ctxt, mk_class_decls = mk_new_classes ctxt ctbl in
    let decls =
      [ import_prelude;
        import_refperm;
        mk_reftype_decl ctbl;
        mk_heap_decl {ctxt with ctbl};
        state_decl ctxt globals ] in
    let img_fns = IdentM.fold (fun f f' decls ->
        let img_fn = mk_image_fn f' in
        let decl_class = match Ctbl.decl_class ctxt.ctbl f with
          | Some cname -> cname
          | _ -> (Id "") in
        match Ctbl.field_type ctxt.ctbl f with
        | Some ty ->
          let img_ax = mk_image_axiom ctxt decl_class f' ty in
          [img_fn; img_ax] @ decls
        | None -> decls
      ) ctxt.field_map [] in
    let has_class_types = mk_has_class_type_predicates ctxt in
    let agreement_preds = mk_agreement_predicates ctxt in
    let decls =
      decls
      @ [is_allocated_predicate]
      @ [is_valid_rgn_predicate]
      @ [typeof_rgn_predicate]
      @ has_class_types
      @ [ok_refperm_decl]
      @ mk_class_decls
      @ img_fns
      @ mk_utility_predicates ctxt
      @ agreement_preds in
    ctxt, Modules [state_module_name, decls]

end


(* -------------------------------------------------------------------------- *)
(* Translation to Why3 parse trees                                            *)
(* -------------------------------------------------------------------------- *)

(* Ptree.term is used for logical terms (formulas and specs) and
   Ptree.expr is used for programs.  Why3's ``pure'' construct allows
   terms to be used in program expressions, but it is not possible to
   embed expressions in terms.  This is unlike our source language,
   where expressions _can_ be used in formulas.  Therefore, we require
   functions that convert source language expressions to both Why3
   program expressions and logical terms.

   Note that source language commands are compiled to Why3
   expressions.
*)

let expr_of_const_exp (e: T.const_exp T.t) =
  match e.node with
  | Enull -> null_const
  | Eemptyset -> mk_qevar empty_rgn
  | Eunit -> mk_expr (Etuple [])
  | Eint i -> mk_econst i
  | Ebool true -> mk_expr Etrue
  | Ebool false -> mk_expr Efalse

let term_of_const_exp (e: T.const_exp T.t) =
  match e.node with
  | Enull -> null_const_term
  | Eemptyset -> mk_qvar empty_rgn
  | Eunit -> mk_term (Ttuple [])
  | Eint i -> mk_tconst i
  | Ebool true -> mk_term Ttrue
  | Ebool false -> mk_term Tfalse

let infix_op_of_binop = function
  | Plus   -> mk_infix "+"
  | Minus  -> mk_infix "-"
  | Mult   -> mk_infix "*"
  | Equal  -> mk_infix "="
  | Nequal -> mk_infix "<>"
  | Leq    -> mk_infix "<="
  | Lt     -> mk_infix "<"
  | Geq    -> mk_infix ">="
  | Gt     -> mk_infix ">"
  | _      -> invalid_arg "infix_op_of_binop"

let expr_of_binop op (e1, e1_ty) (e2, e2_ty) =
  let open T in
  let mk_expr_desc op : Ptree.expr_desc =
    match op with
    | Div   -> Eidapp (div_fn, [e1; e2])
    | And   -> Eand   (e1, e2)
    | Or    -> Eor    (e1, e2)
    | Union -> Eidapp (union_fn, [e1; e2])
    | Inter -> Eidapp (inter_fn, [e1; e2])
    | Diff  -> Eidapp (diff_fn, [e1; e2])
    | Equal -> assert (T.equiv_ity e1_ty e2_ty);
      begin match e1_ty with
        | Tclass _  -> Einfix (e1, mk_infix "=.", e2)
        | Tanyclass -> Einfix (e1, mk_infix "=.", e2)
        | Trgn      -> Eidapp (eq_rgn_fn,  [e1; e2])
        | Tbool     -> Eidapp (eq_bool_fn, [e1; e2])
        | Tunit     -> Eidapp (eq_unit_fn, [e1; e2])
        | _         -> Einfix (e1, mk_infix "=", e2)
      end
    | Nequal -> assert (T.equiv_ity e1_ty e2_ty);
      begin match e1_ty with
        | Tclass _  -> Einfix (e1, mk_infix "<>.", e2)
        | Tanyclass -> Einfix (e1, mk_infix "<>.", e2)
        | Trgn      -> Enot (mk_expr (Eidapp (eq_rgn_fn,  [e1; e2])))
        | Tbool     -> Enot (mk_expr (Eidapp (eq_bool_fn, [e1; e2])))
        | Tunit     -> Enot (mk_expr (Eidapp (eq_unit_fn, [e1; e2])))
        | Tint      -> Enot (mk_expr (Einfix (e1, mk_infix "=", e2)))
        | _         -> Einfix (e1, mk_infix "<>", e2)
      end
    | _     -> Einfix (e1, infix_op_of_binop op, e2) in
  mk_expr (mk_expr_desc op)

let expr_of_unrop op e =
  match op with
  | Not    -> mk_expr (Enot e)
  | Uminus ->
    let zero = mk_econst 0 in
    mk_expr @@ Einfix (zero, mk_ident (Ident.op_infix "-"), e)

let term_of_binop op (e1, e1_ty) (e2, e2_ty) =
  let mk_term_desc op : Ptree.term_desc =
    match op with
    | Div   -> Tidapp (div_fn, [e1; e2])
    | And   -> Tbinop (e1, Dterm.DTand_asym, e2) (* DTand_asym = && *)
    | Or    -> Tbinop (e1, Dterm.DTor_asym, e2)  (* DTor_asym  = || *)
    | Union -> Tidapp (union_fn, [e1; e2])
    | Inter -> Tidapp (inter_fn, [e1; e2])
    | Diff  -> Tidapp (diff_fn, [e1; e2])
    | _     -> Tinfix (e1, infix_op_of_binop op, e2) in
  mk_term (mk_term_desc op)

let term_of_unrop op e =
  match op with
  | Not    -> mk_term (Tnot e)
  | Uminus ->
    let zero = mk_tconst 0 in
    mk_term @@ Tinfix (zero, mk_ident (Ident.op_infix "-"), e)

type 'a exp_interpretation =
  { mk_var: Ptree.qualid -> 'a;
    mk_app: Ptree.qualid -> 'a list -> 'a;
    mk_singleton: 'a -> 'a;
    lookup_id: ctxt -> Ptree.qualid -> ident -> 'a;
    interp_binop: binop -> ('a * T.ity) -> ('a * T.ity) -> 'a;
    interp_unrop: unrop -> 'a -> 'a;
    interp_const_exp: T.const_exp T.t -> 'a;
    state_load: ctxt -> Ptree.qualid -> ident T.t * ident T.t -> 'a;
  }

let as_expr : Ptree.expr exp_interpretation =
  { mk_var = mk_qevar;
    mk_app = mk_eapp;
    lookup_id = lookup_id;
    mk_singleton = (fun e -> singleton_fn <$> [e]);
    interp_binop = expr_of_binop;
    interp_unrop = expr_of_unrop;
    interp_const_exp = expr_of_const_exp;
    state_load = st_load;
  }

let as_term : Ptree.term exp_interpretation =
  { mk_var = mk_qvar;
    mk_app = mk_tapp;
    lookup_id = lookup_id_term;
    mk_singleton = (fun e -> singleton_fn <*> [e]);
    interp_binop = term_of_binop;
    interp_unrop = term_of_unrop;
    interp_const_exp = term_of_const_exp;
    state_load = st_load_term;
  }

let rec interp_exp (interp: 'a exp_interpretation) ctxt state (e: T.exp T.t)
  : 'a =
  match e.node with
  | Econst e -> interp.interp_const_exp e
  | Evar id -> interp.lookup_id ctxt state id.node
  | Ebinop (op, e1, e2) ->
    let e1_ty = e1.ty and e2_ty = e2.ty in
    let e1 = interp_exp interp ctxt state e1 in
    let e2 = interp_exp interp ctxt state e2 in
    interp.interp_binop op (e1, e1_ty) (e2, e2_ty)
  | Eunrop (op, e) ->
    let e = interp_exp interp ctxt state e in
    interp.interp_unrop op e
  | Eimage ({node=Esingleton{node=Evar name;ty=Tclass k};ty=_}, f) (* {x}`f *)
    when Ctbl.decl_class ctxt.ctbl f.node = Some k ->
    begin match Opt.get (Ctbl.field_type ctxt.ctbl f.node) with
      | Trgn -> interp.state_load ctxt state (name, f)
      | Tint | Tbool | Tunit | Tmath _ ->
        interp.interp_const_exp T.(Eemptyset -: Trgn)
      | Tanyclass
      | Tclass _ -> interp.mk_singleton(interp.state_load ctxt state (name, f))
      | Tdatagroup | Tprop | Tmeth _ | Tfunc _ -> assert false
    end 
  | Eimage (g, f) ->
    let g = interp_exp interp ctxt state g in
    let fname = lookup_field ctxt f.node in
    let image_fn = mk_image_fn_qualid fname in
    interp.mk_app image_fn [interp.mk_var state; g]
  | Ecall (fn, args) ->
    let args = map (interp_exp interp ctxt state) args in
    let fk, fn =
      (match IdentM.find fn.node ctxt.ident_map with
       | Id_other, fn -> Id_other, fn
       | Id_extern, fn -> Id_extern, fn
       | _ | exception Not_found ->
         failwith @@ "Unknown symbol: " ^ string_of_ident fn.node) in
    let state_arg = interp.mk_var state in
    (* FIXME: handle generally? *)
    let args = if mem fn [array_get_fn; array_set_fn; array_len_fn]
               || fk = Id_extern
      then args
      else state_arg :: args in
    interp.mk_app fn args
  | Esingleton e ->
    let e = interp_exp interp ctxt state e in
    interp.mk_singleton e

let expr_of_exp = interp_exp as_expr
let term_of_exp = interp_exp as_term

let dbinop_of_connective = function
  | Conj -> Dterm.DTand
  | Disj -> Dterm.DTor
  | Imp  -> Dterm.DTimplies
  | Iff  -> Dterm.DTiff

let dquant_of_quantifier = function
  | Forall -> Dterm.DTforall
  | Exists -> Dterm.DTexists

let term_of_let_bound_value ctxt state (lb: T.let_bound_value T.t)
  : Ptree.term =
  match lb.node with
  | Lloc (y, f) -> st_load_term ctxt state (y, f)
  | Larr (a, i) ->
    let i = term_of_exp ctxt state i in
    st_load_array_term ctxt state a i
  | Lexp e -> term_of_exp ctxt state e

let term_of_let_bind ctxt state (lb: T.let_bind T.t) : Ptree.term =
  let T.{value; is_old; is_init} = lb.node in
  let value_term = term_of_let_bound_value ctxt state value in
  if is_old then mk_old_term value_term
  else if is_init then mk_term (Tat (value_term, init_label))
  else value_term

(* FIXME: All initial labels in method bodies are assumed to be called INIT *)
let rec term_of_formula ctxt state ?(in_spec=false) (f: T.formula)
  : Ptree.term =
  match f with
  | Ftrue -> mk_term Ttrue
  | Ffalse -> mk_term Tfalse
  | Fexp e -> term_of_exp ctxt state e
  | Fnot f -> mk_term @@ Tnot (term_of_formula ctxt state ~in_spec f)
  | Finit e ->
    let value = term_of_let_bound_value ctxt state e in
    if in_spec then mk_old_term value
    else mk_term @@ Tat (value, init_label)
  | Fpointsto (y, f, e) ->
    let y_f = st_load_term ctxt state (y, f) in
    let e' = term_of_exp ctxt state e in
    term_of_binop Equal (y_f, f.ty) (e', e.ty)
  | Farray_pointsto (a, i, e) ->
    let i = term_of_exp ctxt state i in
    let e = term_of_exp ctxt state e in
    let aidx = st_load_array_term ctxt state a i in
    aidx ==. e
  | Fsubseteq (g1, g2) ->
    let g1 = term_of_exp ctxt state g1 in
    let g2 = term_of_exp ctxt state g2 in
    subset_fn <*> [g1; g2]
  | Fdisjoint (g1, g2) ->
    let g1 = term_of_exp ctxt state g1 in
    let g2 = term_of_exp ctxt state g2 in
    disjoint_fn <*> [g1; g2]
  | Fmember (e, {node = Evar {node = Id "alloc"; ty = Trgn}; ty = Trgn}) ->
    let e = term_of_exp ctxt state e in
    let alloct = state %. st_alloct_field in
    map_mem_fn <*> [e; mk_qvar alloct]
  | Fmember (e, g) ->
    let e = term_of_exp ctxt state e in
    let g = term_of_exp ctxt state g in
    mem_fn <*> [e; g]
  | Fold (e, lb) ->
    let value = term_of_let_bound_value ctxt state lb in
    let old_value = mk_old_term value in
    let e = term_of_exp ctxt state e in
    e ==. old_value
  | Ftype (g, ty) ->
    (* ty is expected to be a class name -- we have to emit a
       constructor of reftype *)
    let ty = mk_var @@ mk_reftype_ctor ty in
    let g = term_of_exp ctxt state g in
    typeof_rgn_fn <*> [mk_qvar state; g; ty]
  | Fconn (c, f1, f2) ->
    let f1 = term_of_formula ctxt state ~in_spec f1 in
    let f2 = term_of_formula ctxt state ~in_spec f2 in
    mk_term @@ Tbinop (f1, dbinop_of_connective c, f2)
  | Flet (id, lb, f) ->
    let id' = gen_ident state ctxt (id_name id.node) in
    let lb = term_of_let_bind ctxt state lb in
    let ctxt' = add_logic_ident ctxt id.node id'.id_str in
    mk_term @@ Tlet (id', lb, term_of_formula ctxt' state ~in_spec f)
  | Fquant (q, binds, f) ->
    let q' = dquant_of_quantifier q in
    let ctxt', binders, additional = mk_binders ctxt state binds in
    let f = term_of_formula ctxt' state ~in_spec f in
    match q with
    | Forall -> mk_quant q' binders (mk_implies (additional @ [f]))
    | Exists -> mk_quant q' binders (mk_conjs (additional @ [f]))

(* mk_binders G s qbinds = (G', binders, antecedents)

   G' adds each binder in qbinds to G, binders is a list of
   Ptree.binder's used to build a Why3 quantified formula, and
   antecedents is a list of Ptree.term's.
*)
and mk_binders ?(prefix="") ctxt state binds
  : ctxt * Ptree.binder list * Ptree.term list =
  let open Build_State in
  let has_ctype = has_class_type_pred in
  List.fold_right (fun (id, eopt) (ctxt, binders, ants) ->
      let T.{node; ty} = id in
      let id' = gen_ident state ctxt (prefix ^ id_name id.node) in
      let pty = pty_of_ty ty in
      match eopt, ty with
      | Some rgn, Tclass k ->
        assert (Ctbl.class_exists ctxt.ctbl k);
        let id'_term = mk_var id' in
        let rgn = term_of_exp ctxt state rgn in
        let id'_type = (has_ctype k) <*> [mk_qvar state; id'_term] in
        let alloc'd = is_allocated_pred <*> [mk_qvar state; id'_term] in
        let in_rgn = mk_tapp mem_fn [id'_term; rgn] in
        let ctxt = add_logic_ident ctxt id.T.node id'.id_str in
        let binder = mk_binder id' false (Some pty) in
        (ctxt, binder :: binders, [alloc'd; id'_type; in_rgn] @ ants)
      | Some _, _ -> invalid_arg ("mk_binders: " ^ T.string_of_ity ty)
      | None, Tclass k ->
        assert (Ctbl.class_exists ctxt.ctbl k);
        let id'_term = mk_var id' in
        let id'_type = (has_ctype k) <*> [mk_qvar state; id'_term] in
        let alloc'd = is_allocated_pred <*> [mk_qvar state; id'_term] in
        let ctxt = add_logic_ident ctxt id.T.node id'.id_str in
        let binder = mk_binder id' false (Some pty) in
        (ctxt, binder :: binders, [alloc'd; id'_type] @ ants)
      | None, _ ->
        let ctxt = add_logic_ident ctxt id.T.node id'.id_str in
        let binder = mk_binder id' false (Some pty) in
        (ctxt, binder :: binders, ants)
    ) binds (ctxt, [], [])

let rec expr_of_atomic_command ctxt state (ac: T.atomic_command) : Ptree.expr =
  let mk_exp var = T.Evar var -: var.ty in
  let ppstr pf e =
    let () = pf Format.str_formatter e in
    Format.flush_str_formatter () in
  let msg = ppstr pp_atomic_command_special ac in
  match ac with
  | Skip -> mk_expr (Etuple [])
  | Assign (id, e) ->
    let e = expr_of_exp ctxt state e in
    update_id ~msg ctxt state id.node e
  | New_class (id, k) ->
    let fn   = mk_alloc_name k in
    let call = mk_eapp (qualid_of_ident fn) [mk_qevar state] in
    update_id ~msg ctxt state id.node call
  | New_array (a, k, len) -> compile_new_array msg ctxt state a k len
  | Field_deref (y, x, f) ->  (* y := x.f *)
    let field_val = st_load ctxt state (x, f) in
    update_id ~msg ctxt state y.node field_val
  | Field_update (x, f, e) -> (* x.f := e *)
    let exp_val = expr_of_exp ctxt state e in
    st_store ~msg ctxt state (x.node, f.node) exp_val
  | Array_access (x, a, idx) -> (* x := a[idx] *)
    let idx = expr_of_exp ctxt state idx in
    let elt = st_load_array ctxt state a idx in
    update_id ~msg ctxt state x.node elt
  | Array_update (a, idx, e) -> (* a[idx] := e *)
    let idx = expr_of_exp ctxt state idx in
    let rhs = expr_of_exp ctxt state e in
    st_store_array ~msg ctxt state a idx rhs
  | Call (idopt, meth, args) ->
    let args = map (expr_of_exp ctxt state % mk_exp) args in
    let meth_kind, meth = match IdentM.find meth.node ctxt.ident_map with
      | Id_other, meth -> Id_other, meth
      | Id_extern, meth -> Id_extern, meth
      | _ | exception Not_found ->
        let meth_name = string_of_ident meth.node in
        failwith ("Unknown method " ^ meth_name) in
    let state_arg = mk_qevar state in
    (* FIXME: handle generally? *)
    let args = if mem meth [array_get_fn; array_set_fn; array_len_fn]
               || meth_kind = Id_extern
      then args
      else state_arg :: args in
    let call = mk_eapp meth args in
    begin match idopt with
      | Some id -> update_id ~msg ctxt state id.node call
      | None -> explain_expr call msg
    end

and compile_new_array msg ctxt state a k len =
  let length = fst (Opt.get (Ctbl.array_like_length_field ctxt.ctbl k)) in
  let slots  = fst (Opt.get (Ctbl.array_like_slots_field ctxt.ctbl k)) in
  let elt_ty = Opt.get (Ctbl.element_type ctxt.ctbl k) in
  let len_expr  = expr_of_exp ctxt state len in
  let mk_array  = mk_alloc_name k in
  let alloc_obj = mk_eapp (qualid_of_ident mk_array) [mk_qevar state] in
  let array_val = mk_eapp array_make_fn [len_expr; default_value ctxt elt_ty] in
  let e1 = update_id ~msg ctxt state a.node alloc_obj in
  let e2 = st_store ~msg ctxt state (a.node, length) len_expr in
  let e3 = st_store ~msg ctxt state (a.node, slots) array_val in
  mk_expr (Esequence (e1, mk_expr (Esequence (e2, e3))))

(* Turn a series of conjuncts into a list of formulas.  Arguably helps
   make emitted loop invariants easier to read.  Why3 allows having
   muliple invariant clauses in a while loop.  This is not allowed in
   our source language.
*)
let rec split_conjuncts (frm: T.formula) : T.formula list =
  match frm with
  | Fconn(Conj, f1, f2) -> split_conjuncts f1 @ split_conjuncts f2
  | _ -> [frm]

let rec expr_of_command ctxt state (c: T.command) : Ptree.expr =
  match c with
  | Acommand ac -> expr_of_atomic_command ctxt state ac
  | Vardecl (id, modif, ty, com) ->
    let id_val = default_value ctxt ty in
    let id_val = mk_expr @@ Eapply (mk_expr Eref, id_val) in
    let id' = gen_ident state ctxt (id_name id.node) in
    let ghost = (match modif with Some Ghost -> true | _ -> ty = Trgn) in
    let ctxt = add_local_ident ty ctxt id.node id'.id_str in
    let body = expr_of_command ctxt state com in
    let body = begin match local_intro_assert ctxt state id ty with
      | None -> body
      | Some asrt -> mk_expr @@ Esequence (asrt, body)
    end in
    mk_expr @@ Elet (id', ghost, Expr.RKnone, id_val, body)
  | Seq (c1, c2) ->
    let c1 = expr_of_command ctxt state c1 in
    let c2 = expr_of_command ctxt state c2 in
    mk_expr @@ Esequence (c1, c2)
  | If (guard, conseq, alter) ->
    let guard = expr_of_exp ctxt state guard in
    let conseq = expr_of_command ctxt state conseq in
    let alter = expr_of_command ctxt state alter in
    mk_expr @@ Eif (guard, conseq, alter)
  | While (guard, inv, body) ->
    let guard = expr_of_exp ctxt state guard in
    let invs = map (term_of_formula ctxt state) (split_conjuncts inv) in
    let locty_conds = safe_mk_conjs @@ locals_ty_loop_invariant ctxt state in
    let locty_conds = match locty_conds with
      | [] -> []
      | [inv] -> [explain_term inv "locals type invariant"]
      | _ -> assert false in
    let invs = locty_conds @ [alloc_does_not_shrink state] @ invs in
    let body = expr_of_command ctxt state body in
    mk_expr @@ Ewhile (guard, invs, [], body)
  | Assume f -> mk_expr @@ Eassert (Expr.Assume, term_of_formula ctxt state f)
  | Assert f -> mk_expr @@ Eassert (Expr.Assert, term_of_formula ctxt state f)

and local_type_cond ctxt state v ity : Ptree.term option =
  let open Build_State in
  let state' = mk_qvar state in
  let v' = lookup_id_term ctxt state v.T.node in
  match ity with
  | T.Tclass k -> Some (has_class_type_pred k <*> [state'; v'])
  | T.Trgn -> Some (is_valid_rgn_pred <*> [state'; v'])
  | _ -> None

and local_intro_assert ctxt state v ity : Ptree.expr option =
  let open Lib.Opt.Monad_syntax in
  let* cond = local_type_cond ctxt state v ity in
  Lib.Opt.some (mk_expr (Eassert (Expr.Assert, cond)))

and locals_ty_loop_invariant ctxt state : Ptree.term list =
  let rec loop aux = function
    | [] -> rev aux
    | (k, (ity, _)) :: rest ->
      begin match local_type_cond ctxt state (k -: ity) ity with
        | None -> loop aux rest
        | Some cond -> loop (cond :: aux) rest
      end in
  let locals = ctxt_locals ctxt in
  loop [] locals

and alloc_does_not_shrink state : Ptree.term =
  let old_state = mk_old_term (mk_qvar state) in
  let pred = qualid_of_ident (Build_State.alloc_does_not_shrink) in
  pred <*> [old_state; mk_qvar state]

(* mk_wr_frame_of_field ctxt s r f emits:

   forall p:reference.
     mem p (old s.alloct) ->
     not (mem p r) ->
     find p s.alloct = DeclClass(f) ->
     find p s.heap.f = find p (old s.heap.f)
*)
let rec mk_wr_frame_of_field ctxt state rgn field : Ptree.term =
  assert (Ctbl.field_exists ctxt.ctbl field);
  let field_ty = Opt.get (Ctbl.field_type ctxt.ctbl field) in
  match Ctbl.decl_class ctxt.ctbl field with
  | Some cname ->
    let expl = "write frame " ^ string_of_ident field in
    let term =
      let+! p,_ = bindvar (gen_ident state ctxt "p", reference_type) in
      let ctxt = add_logic_ident ctxt (Id "p") p.id_str in
      let oalloct = mk_old_term (mk_qvar (state %. st_alloct_field)) in
      let palloc = map_mem_fn <*> [~*p; oalloct] in
      let not_pmem = mk_wr_frame_not_in_rgn p rgn in
      let of_type = st_has_type state (~*p) cname in
      let loc = (Id "p" -: Tclass cname, field -: field_ty) in
      let fval = st_load_term ctxt state loc in
      let old_fval = st_load_old ctxt state (Id "p", field) in
      let unchanged = fval ==. old_fval in
      if not_pmem = mk_term Ttrue
      then return (palloc ^==> of_type ^==> unchanged)
      else return (palloc ^==> of_type ^==> not_pmem ^==> unchanged) in
    explain_term (build_term term) expl
  | None ->
    failwith ("mk_wr_frame_of_field: Unknown field " ^ string_of_ident field)

(* Produce not (mem p rgn) with minor simplifications.  If rgn = {e},
   then produce (p <> e); and if rgn = {}, produce True.
*)
and mk_wr_frame_not_in_rgn p rgn =
  let rgn = simplify_region rgn in
  match rgn.Ptree.term_desc with
  | Ptree.Tidapp (mk, [t]) when mk = mk_set_fn ->
    begin match t.term_desc with
      | Ptree.Tidapp (sngl, [inner_t]) when sngl = singleton_fn ->
        (~*p) =/=. inner_t
      | _ -> rgn
    end
  | Ptree.Tidapp (sngl, [exp]) when sngl = singleton_fn -> (~*p) =/=. exp
  | Ptree.Tident emp when emp = empty_rgn -> mk_term Ttrue
  | _ -> mk_term (Tnot (mem_fn <*> [~*p; rgn]))

(* Replace p union {} by p; {} union p by p; {} union {} by empty *)
and simplify_region rgn =
  match rgn.Ptree.term_desc with
  | Ptree.Tidapp (union_fn, [e1; e2]) ->
    let e1' = simplify_region e1 in
    let e2' = simplify_region e2 in
    begin match e1'.Ptree.term_desc, e2'.Ptree.term_desc with
      | Ptree.Tident emp, Ptree.Tident emp'
        when emp = empty_rgn && emp' = empty_rgn -> mk_qvar empty_rgn
      | Ptree.Tident emp, _ when emp = empty_rgn -> e2'
      | _, Ptree.Tident emp when emp = empty_rgn -> e1'
      | _, _ -> mk_term (Tidapp (union_fn, [e1'; e2']))
    end
  | _ -> rgn

(* get_wr_effects es = es'

   Invariant:
   es' = all the writes in es
*)
let get_wr_effects (effects: T.effect) =
  filter (fun e ->
      match T.(e.effect_kind) with
      | Write -> true
      | Read  -> false
    ) effects

let only_writes_to_imgs (effects: T.effect) =
  let open T in
  forall (fun e ->
      match e.effect_kind, e.effect_desc.node with
      | Write, Effimg _ -> true
      | _ -> false
    ) effects

let mk_wr_frame_condition ctxt state (effects: T.effect) : Ptree.term list =
  (* FIXME: update
     Steps:
     1. Collect all the wr effects
     2. Expand datagroups -- turn {f}`grp to {f}`f1, {f}`f2, ...,
        {f}`fn for all fields f1...fn in grp.  The required
        information is stored in ctxt.dgrps_map.
     3. Collect all expressions with the same fields.  If we have
        {f}`val, {g}`rep, {h}`val, then create {f,h}`val, {g}`rep
     4. For each of these, mk_wr_frame_field to obtain a list of
        Why3 terms.
  *)
  let open T in
  let writes = get_wr_effects effects in
  let wr_to_alloc e = match e.effect_desc.node with
    | Effvar {node = Id "alloc"; ty = Trgn} -> e.effect_desc.ty = Trgn
    | _ -> false in
  let alloc_cond =
    if not (exists wr_to_alloc writes) then []
    else [alloc_does_not_shrink state] in
  let wr_imgs = filter (fun e -> is_eff_img e.effect_desc) writes in
  alloc_cond @ map (fun e ->
      match e.effect_desc.node with
      | Effimg (g, fld) ->
        let g_term = term_of_exp ctxt state g in
        mk_wr_frame_of_field ctxt state g_term fld.node
      | Effvar _ -> assert false
    ) wr_imgs

let rec compile_spec ctxt state (s: T.spec) : Ptree.spec =
  let open T in
  let open List in
  let rec walk pre post effs = function
    | [] -> (pre, post, effs)
    | Precond (f) :: spec -> walk (f::pre) post effs spec
    | Postcond (f) :: spec -> walk pre (f::post) effs spec
    | Effects e :: spec -> walk pre post (e::effs) spec in
  let pre, post, effs = walk [] [] [] (rev s) in
  let comp_f f = term_of_formula ctxt ~in_spec: true state f in
  let pre, post = map_pair (map comp_f) (pre, post) in
  let post = map mk_ensures post in
  let conds = concat_map (mk_wr_frame_condition ctxt state) effs in
  let conds = map mk_ensures conds in
  let writes = compile_writes ctxt state (flatten effs) in
  mk_spec pre (conds @ post) [] writes

and compile_writes ctxt state (eff: T.effect) : Ptree.term list =
  let open T in
  let resolve_field f =
    (* FIXME: do we really need field_map anymore? *)
    let f = f.node in
    match IdentM.find f ctxt.field_map with
    | fld -> fld
    | exception Not_found -> ~. (id_name f) in
  let to_term = function
    | Effimg (_, f) -> mk_qvar (state %. st_heap_field %. (resolve_field f))
    | Effvar {node = Id "alloc"; _} -> mk_qvar (state%. st_alloct_field)
    | Effvar x -> lookup_id_term ctxt state x.node in
  map (to_term % (fun e -> e.effect_desc.node)) (wrs eff)

(* Emit a Ptree.param list from an T.param_info list.  Additionally,
   for each p in ps such that p is of a non-null type, generate the
   appropriate formula.  Requires ps to be well-formed in the sense
   that only class types are annotated as non-null. *)
let rec params_of_param_info_list ?(prefix="") state ps
  : Ptree.param list * Ptree.term list =
  let open T in
  let open Lib.Opt.Monad_syntax in
  let loop param (params, obligations) =
    let {param_name; param_ty; is_non_null} = param in
    let param_name = id_name param_name.node in
    let name = mk_ident (prefix ^ param_name) in
    let pty = pty_of_ty param_ty in
    let param = mk_param name false pty in
    match param_ty with
    | Tclass cname ->
      let cpred = Build_State.has_class_type_pred cname in
      let objp = cpred <*> [mk_qvar state; ~*name] in
      let nnull = if is_non_null then [(~*name) =/=. null_const_term] else [] in
      param :: params, objp :: nnull @ obligations
    | _ -> param :: params, obligations in
  foldr loop ([], []) ps

let rec params_of_param_list ?(prefix="") ctxt state ps
  : Ptree.param list * Ptree.term list =
  let loop (ident, ty) (params, antecedents) =
    let pty = pty_of_ty ty in
    let name = gen_ident state ctxt (prefix ^ id_name ident) in
    let param = mk_param name false pty in
    if is_class_ty ty then begin
      let state = mk_qvar state in
      let cname = match ty with Tclass k -> k | _ -> assert false in
      let pred_fn = Build_State.has_class_type_pred cname in
      let pre = pred_fn <*> [state; ~*name] in
      (param :: params, pre :: antecedents)
    end else (param :: params, antecedents) in
  foldr loop ([], []) ps

let binder_of_param (p: Ptree.param) : Ptree.binder =
  let (loc, name, ghost, ty) = p in
  (loc, name, ghost, Some ty)

let rec add_parameters ?(prefix="") ctxt params : ctxt =
  let loop p ctxt =
    let T.{param_name; _} = p in
    let name = id_name param_name.node in
    add_ident Id_other ctxt param_name.node (prefix ^ name) in
  foldr loop ctxt params

let compile_axiom_or_lemma ctxt state_ident kind name body : Ptree.decl =
  let state = mk_qualid [state_ident.Ptree.id_str] in
  let body = term_of_formula ctxt state body in
  let state_binder = mk_binder state_ident false (Some state_type) in
  let body = mk_term @@ Tquant (DTforall, [state_binder], [], body) in
  (* FIXME: other methods rely on having name in the ctxt.  Should
     this function return a ctxt and a decl? *)
  let name = mk_ident @@ id_name name in
  match kind with
  | `Axiom ->
    let name = { name with id_ats = [Ptree.ATstr Ident.useraxiom_attr] } in
    Dprop (Decl.Paxiom, name, body)
  | `Lemma -> Dprop (Decl.Plemma, name, body)

let compile_named_formula ctxt (nf: T.named_formula) : Ptree.decl =
  reset_fresh_id ();
  let name = nf.formula_name in
  let body = nf.body in
  let state_ident = ~. (fresh_name ctxt "s") in
  let state = mk_qualid [state_ident.id_str] in
  match nf.kind with
  | `Axiom | `Lemma as k ->
    compile_axiom_or_lemma ctxt state_ident k name.node body
  | `Predicate ->
    let name = id_name name.node in
    let params = map (fun T.{node;ty} -> (node,ty)) nf.params in
    let params, antecedents = params_of_param_list ctxt state params in
    let state_param = mk_param state_ident false state_type in
    let ctxt = foldr (fun (T.{node=id;_}, (_,name,_,_)) ctxt ->
        let name = Opt.get name in
        add_ident Id_other ctxt id name.Ptree.id_str
      ) ctxt (zip nf.params params) in
    let ctxt = add_ident Id_other ctxt nf.formula_name.node name in
    let body = term_of_formula ctxt state nf.body in
    let ext_body = mk_implies (antecedents @ [body]) in
    let ldecl = Ptree.{
        ld_loc = Loc.dummy_position;
        ld_ident = mk_ident name;
        ld_params = state_param :: params;
        ld_type = None;
        ld_def = Some ext_body
      } in
    Dlogic [ldecl]

type meth_compile_info = {
  mci_name: Ptree.ident;
  mci_ctxt: ctxt;
  mci_state: Ptree.qualid;
  mci_params: Ptree.param list;
  mci_spec: Ptree.spec;
  mci_ret_ty: Ptree.pty;
}

(* FIXME: Have to take care when deciding what the Why3 name for m
   would be -- the call command may use a qualified identifier to
   refer to this method (if it is imported from another module). *)
let compile_meth_aux ctxt (m: T.meth_decl) : meth_compile_info =
  reset_fresh_id ();
  let meth_name =
    let name = m.meth_name.node in
    if Ctbl.class_exists ctxt.ctbl name
    then mk_ctor_name name
    else mk_ident @@ id_name name in
  let ret_ty = pty_of_ty m.result_ty in
  let result = Id_other, mk_qualid ["result"] in
  let ident_map = IdentM.add (Id "result") result ctxt.ident_map in
  let ctxt = { ctxt with ident_map } in
  let ctxt = add_parameters ctxt m.params in
  let state_ident = ~. (fresh_name ctxt "s") in
  let state = mk_qualid [state_ident.id_str] in
  let params, extra_pre = params_of_param_info_list state m.params in
  let state_param = Loc.dummy_position, Some state_ident, false, state_type in
  let params = state_param :: params in
  let meth_spec = compile_spec ctxt state m.meth_spec in
  let precond = extra_pre @ meth_spec.sp_pre in
  let meth_spec = { meth_spec with sp_pre = precond } in
  let extra_non_null_post =
    if m.result_ty_is_non_null
    then [mk_ensures ( (~* (~. "result")) =/=. null_const_term )]
    else [] in
  let extra_trivial_post =
    if m.result_ty = Tunit
    then [mk_ensures ((~* (~. "result")) ==. (mk_term (Ttuple [])))]
    else [] in
  let extra_ty_post = match m.result_ty with
    | Tclass k ->
      let cpred = Build_State.has_class_type_pred k in
      [mk_ensures (cpred <*> [mk_qvar state; ~* (~."result")])]
    | _ -> [] in
  let extra_post = extra_non_null_post @ extra_trivial_post @ extra_ty_post in
  let meth_spec = { meth_spec with sp_post = extra_post @ meth_spec.sp_post } in
  { mci_name = meth_name;
    mci_ctxt = ctxt;
    mci_spec = meth_spec;
    mci_state = state;
    mci_params = params;
    mci_ret_ty = ret_ty
  }

let mk_efun mci body : Ptree.expr =
  let {mci_name; mci_params; mci_spec; mci_ret_ty; _} = mci in
  let binders = map binder_of_param mci_params in
  let pat = mk_pat Pwild in
  let ret = Some mci_ret_ty in
  let mask = Ity.MaskVisible in
  mk_expr @@ Efun (binders, ret, pat, mask, mci_spec, body)

let rec copy_args_and_compile_body ctxt state params ret com : Ptree.expr =
  (* add_to_expr E fin = E'

     Invariant:
     If E is a let or a sequence, then fin is the last expression in E'.
  *)
  let open T in
  let rec add_to_expr expr fin : Ptree.expr =
    match Ptree.(expr.expr_desc) with
    | Elet (id, gho, knd, value, body) ->
      mk_expr @@ Elet (id, gho, knd, value, add_to_expr body fin)
    | Esequence (e1, e2) ->
      mk_expr @@ Esequence (e1, add_to_expr e2 fin)
    | _ -> mk_expr @@ Esequence (expr, fin) in
  let rec loop ctxt = function
    | [] ->
      let fin = lookup_id ctxt state (Id "result") in
      add_to_expr (expr_of_command ctxt state com) fin
    | {param_name; param_ty; _} :: ps ->
      let name = id_name param_name.node in
      let copy = mk_expr @@ Eapply (mk_expr Eref, mk_evar (mk_ident name)) in
      let ctxt = add_local_ident param_ty ctxt param_name.node name in
      mk_expr (Elet (mk_ident name, false, Expr.RKnone, copy, loop ctxt ps)) in
  loop (add_local_ident ret ctxt (Id "result") "result") params

type sp_precond = T.formula list
type sp_postcond = T.formula list
type sp_effect = T.effect

let create_spec pre post eff =
  let pre' = map (fun f -> T.Precond f) pre in
  let post' = map (fun f -> T.Postcond f) post in
  let eff' = T.Effects eff in
  pre' @ post' @ [eff']

let alloc_in_writes (eff: T.effect) =
  let p e = match T.dest_eff e with
    | (Write, {node = Effvar x; _}) -> x.node = Id "alloc"
    | _ -> false in
  exists p eff

let rec compile_meth_def ctxt (m: T.meth_def) : ctxt * Ptree.decl =
  let Method (mdecl, mbody) = m in
  match mbody with
  | None ->
    let mci = compile_meth_aux ctxt mdecl in
    let e = mk_abstract_expr mci.mci_params mci.mci_ret_ty mci.mci_spec in
    let wrs = specified_writes mci.mci_spec in
    let meth_qualid = qualid_of_ident mci.mci_name in
    let meth_wrs = QualidM.add meth_qualid wrs ctxt.meth_wrs in
    let ctxt = {ctxt with meth_wrs} in
    ctxt, Dlet (mci.mci_name, false, Expr.RKnone, e)
  | Some com ->
    let alloc'd = classes_instantiated ctxt com in
    let inst_map = IdentM.add mdecl.meth_name.node alloc'd ctxt.inst_map in
    let ctxt = {ctxt with inst_map} in
    let alloc'd = IdentS.elements alloc'd in
    let extra_wrs = concat_map (fresh_obj_wrs ctxt.ctbl) alloc'd in
    let meth_spec = T.Effects extra_wrs :: mdecl.meth_spec in
    let mpre, mpost, meff = partition_spec meth_spec in
    let meff = Normalize_effects.normalize_effect meff in
    let meth_spec = create_spec mpre mpost meff in
    let mdecl = {mdecl with meth_spec} in
    (* Now we generate all the required frame conditions *)
    let mci = compile_meth_aux ctxt mdecl in
    let ctxt = mci.mci_ctxt in
    (* let ctxt = add_local_ident ctxt (Id "result") "result" in *)
    let state = mci.mci_state in
    let res_ty = mdecl.result_ty in
    let body = copy_args_and_compile_body ctxt state mdecl.params res_ty com in
    let res_val = default_value ctxt mdecl.result_ty in
    let res_val = mk_expr @@ Eapply (mk_expr Eref, res_val) in
    let res_id = mk_ident "result" in
    let res = mk_expr (Elet (res_id, false, Expr.RKnone, res_val, body)) in
    (* Introduce label INIT *)
    let res = mk_expr (Elabel (init_label, res)) in
    let wrttn = fields_written ctxt body in
    let spec_writes = specified_writes mci.mci_spec in
    (* It's important that we only consider the intersection of spec_writes
       and wrttn; otherwise, we may inadvertently add writes not in the spec
       to Why3's write clause.  This can happen when the spec doesn't fully
       specify all the write effects.

       Of course, this must be union'd with extra writes that show up because
       the method allocates objects. *)
    let extra_flds = fields_of_fresh_obj_wrs ctxt state extra_wrs in
    let extra_flds =
      (* A direct write to alloct never shows up in the Why3 method body.
         But, if an object has been allocated we assume it does.
         This is to avoid removing the write to state.alloct. *)
      if alloc'd <> [] && (alloc_in_writes meff)
      then QualidS.add (state %. st_alloct_field) extra_flds
      else extra_flds in
    let wrs = QualidS.(union (inter wrttn spec_writes) extra_flds) in

    if !trans_debug then begin
      let open Printf in
      let meth_name = string_of_ident mdecl.meth_name.node in
      let spec' = QualidS.elements spec_writes in
      let wrttn' = QualidS.elements wrttn in
      let wrs' = QualidS.elements wrs in
      let pp outf =
        let fn = String.concat "." % string_list_of_qualid in
        List.iter (fprintf outf "%s " % fn) in
      fprintf stderr "\nSpecified writes for %s: %a\n" meth_name pp spec';
      fprintf stderr "Actually written in %s: %a\n" meth_name pp wrttn';
      fprintf stderr "Writes emitted for %s: %a\n" meth_name pp wrs';
    end;

    let meth_qualid = qualid_of_ident mci.mci_name in
    let meth_wrs = QualidM.add meth_qualid wrs ctxt.meth_wrs in
    let ctxt = {ctxt with meth_wrs} in
    let wrs = terms_of_fields_written wrs in
    let mci = {mci with mci_spec = {mci.mci_spec with sp_writes = wrs}} in
    let def = mk_efun mci res in
    ctxt, Dlet (mci.mci_name, false, Expr.RKnone, def)

and partition_spec spec : sp_precond * sp_postcond * sp_effect =
  let open T in
  let rec aux pre post effs = function
    | [] -> rev pre, rev post, rev effs
    | Precond f :: rest -> aux (f :: pre) post effs rest
    | Postcond f :: rest -> aux pre (f :: post) effs rest
    | Effects e :: rest -> aux pre post (e @ effs) rest in
  aux [] [] [] spec

and fields_written ctxt com : QualidS.t =
  let ignore_fns = [get_ref_fn; set_ref_fn; map_mem_fn; map_find_fn;
                    array_get_fn; array_set_fn; array_make_fn; array_len_fn] in
  let open QualidS in
  match com.expr_desc with
  | Eassign [{expr_desc = Eident f; _}, None, _] ->
    (* emitted by st_store, update_id; "base case" *)
    singleton f
  | Esequence (e1,e2) -> union (fields_written ctxt e1) (fields_written ctxt e2)
  | Elet (_,_,_,_,e) -> fields_written ctxt e
  | Eif (_,c1,c2) -> union (fields_written ctxt c1) (fields_written ctxt c2)
  | Ewhile (_,_,_,e) -> fields_written ctxt e
  | Eattr (_,e) | Elabel (_,e) -> fields_written ctxt e
  | Eidapp (fn_name, args) -> begin
      let argwrs = List.map (fields_written ctxt) args in
      let argwrs = foldr QualidS.union QualidS.empty argwrs in
      if List.mem fn_name ignore_fns
      then argwrs
      else
        try
          let fn_writes = QualidM.find fn_name ctxt.meth_wrs in
          QualidS.union fn_writes argwrs
        with Not_found ->
          if !trans_debug then
            Printf.fprintf stderr
              "[WARNING] Unable to find writes emitted for %s\n"
              (String.concat "." (string_list_of_qualid (fn_name)));
          argwrs
    end
  | _ -> empty

and terms_of_fields_written qs : Ptree.term list =
  let qs' = QualidS.elements qs in
  map mk_qvar qs'

and specified_writes spec : QualidS.t =
  let writes = spec.sp_writes in
  let fields =
    concat_map (fun e ->
        match e.Ptree.term_desc with
        | Tident i -> [i]
        | Tidapp (fn, [{term_desc = Tident i; _}]) ->
          (* This case should not show up.  lookup_id_term
             returns !x only when x is a local and the meth
             spec effects clause may not reference any locals.
          *)
          assert false
        | _ -> []
      ) writes in
  QualidS.of_list fields

and classes_instantiated ctxt com : IdentS.t =
  let open IdentS in
  let rec walk = T.(function
      | Acommand (New_class (_, k)) -> singleton k
      | Acommand (New_array (_, k, _)) -> singleton k
      | Acommand (Call (_, meth, _)) -> begin
        try IdentM.find meth.node ctxt.inst_map
        with Not_found -> empty
      end
      | Vardecl (_, _, _, c)
      | While (_, _, c) -> walk c
      | Seq (c1, c2)
      | If (_, c1, c2) -> union (walk c1) (walk c2)
      | _ -> empty) in
  walk com

and fresh_obj_wrs ctbl classname : T.effect =
  assert (Ctbl.class_exists ctbl classname);
  let mk_empty_wr f =
    let desc = T.(Effimg (Econst (Eemptyset -: Trgn) -: Trgn, f) -: Trgn) in
    T.{effect_kind = Write;
       effect_desc = desc} in
  let fields = Ctbl.annot_fields ctbl classname in
  map mk_empty_wr fields

and fields_of_fresh_obj_wrs ctxt state (eff: T.effect) : QualidS.t =
  let open QualidS in
  match eff with
  | [] -> empty
  | {effect_kind = Write; effect_desc = desc} :: es ->
    assert (
      match desc.node with
      | T.Effimg ({node=Econst {node=Eemptyset; _}}, _) -> true
      | _ -> false
    );
    begin match desc.node with
      | Effimg (_, f) ->
        let f = simple_resolve_field ctxt f.node in
        let fld = state %. st_heap_field %. f in
        union (singleton fld) (fields_of_fresh_obj_wrs ctxt state es)
      | Effvar _ -> assert false
    end
  | _ -> invalid_arg "fields_of_fresh_obj_wrs: expected write effect"

let mlw_name = function
  | Id name -> mk_ident name
  | Qualid _ -> invalid_arg "mlw_name: expected a non-qualified ident"

type mlw_ctxt =
  | Unary of ctxt
  | Relational of bi_ctxt

type mlw_frag =
  | Compiled of mlw_ctxt * Ptree.mlw_file
  | Uncompiled of T.program_elt

type mlw_map = mlw_frag IdentM.t

let mlw_map_of_penv (penv: T.penv) : mlw_map =
  IdentM.map (fun e -> Uncompiled e) penv

let get_mlw_context mlw_map name =
  match IdentM.find name mlw_map with
  | Compiled (ctxt, _) -> ctxt
  | Uncompiled _ -> invalid_arg "get_mlw_context"

let get_mlw_file mlw_map name =
  match IdentM.find name mlw_map with
  | Compiled (_, mlw_file) -> mlw_file
  | Uncompiled _ -> invalid_arg "get_mlw_file"

let get_unary_ctxt = function
  | Unary ctxt -> ctxt
  | Relational _ -> invalid_arg "get_unary_ctxt"

let standard_imports = [
  import_prelude;
  use_import [Build_State.state_module_name.id_str]
]

let add_extern_to_ctxt ctxt ext_decl : ctxt =
  let open T in
  match ext_decl with
  | Extern_type (_, name)
  | Extern_const (name, _)
  | Extern_axiom name
  | Extern_lemma name
  | Extern_predicate {name; _}
  | Extern_function {name; _} -> add_ident Id_extern ctxt name (id_name name)

let rec compile_interface mlw_map ctxt intr : mlw_map =
  let open T in
  let walk ctxt = function
    | Intr_formula nf ->
      let decl = compile_named_formula ctxt nf in
      let name = nf.formula_name.node in
      let ctxt = add_ident Id_other ctxt name (id_name name) in
      ctxt, Some decl, mlw_map
    | Intr_mdecl mdecl ->
      let mdef = Method (mdecl, None) in
      let ctxt, decl = compile_meth_def ctxt mdef in
      let meth_name =
        if Ctbl.class_exists ctxt.ctbl mdecl.meth_name.node
        then mk_ctor_name mdecl.meth_name.node
        else mk_ident (id_name mdecl.meth_name.node) in
      let ident_map =
        IdentM.add mdecl.meth_name.node (Id_other, mk_qualid [meth_name.id_str])
          ctxt.ident_map in
      let ctxt = {ctxt with ident_map} in
      ctxt, Some decl, mlw_map
    | Intr_extern ex -> add_extern_to_ctxt ctxt ex, None, mlw_map
    | Intr_import import ->
      let ctxt, decl, mlw_map = compile_interface_import mlw_map ctxt import in
      ctxt, Some decl, mlw_map
    | _ -> ctxt, None, mlw_map in
  match IdentM.find intr.intr_name mlw_map with
  | Compiled _ -> mlw_map
  | _ ->
    let ctxt, decls, mlw_map = foldl (fun elt (ctxt, decls, _) ->
        let new_ctxt, decl, mlw = walk ctxt elt in
        match decl with
        | None -> (new_ctxt, decls, mlw)
        | Some decl -> (new_ctxt, decl :: decls, mlw)
      ) (ctxt, [], mlw_map) intr.intr_elts in
    let decls = standard_imports @ rev decls in
    let mlw_file = Ptree.Modules [mlw_name intr.intr_name, decls] in
    let update_fn = const (Some (Compiled (Unary ctxt, mlw_file))) in
    IdentM.update intr.intr_name update_fn mlw_map
  | exception Not_found ->
    failwith ("Not_found: " ^ (string_of_ident intr.intr_name))

and compile_interface_import mlw_map ctxt import_direc
  : ctxt * Ptree.decl * mlw_map =
  let kind, import, as_name = import_direc in
  let import' = qualid_of_ident (mlw_name import) in
  let as_name' = Opt.map (mk_ident % id_name) as_name in
  let node = [import', as_name'] in
  let import_decl = Ptree.Duseimport (Loc.dummy_position, false, node) in
  match kind with
  | Itheory ->
    let import_fname = String.lowercase_ascii (id_name import) in
    let import_decl = use_export [import_fname; id_name import] in
    ctxt, import_decl, mlw_map
  | Iregular ->
    assert (IdentM.mem import mlw_map);
    match IdentM.find import mlw_map with
    | Compiled (Unary ctxt', _) ->
      let ctxt' = qualify_ctxt ctxt' (id_name import) in
      merge_ctxt ctxt ctxt', import_decl, mlw_map
    | Uncompiled (Unary_interface idef) ->
      let new_mlw = compile_interface mlw_map ctxt idef in
      assert (IdentM.mem import new_mlw);
      begin match get_mlw_context new_mlw import with
        | Unary ctxt' ->
          let ctxt' = qualify_ctxt ctxt' (id_name import) in
          merge_ctxt ctxt ctxt', import_decl, new_mlw
        | _ -> assert false
      end
    | _ | exception Not_found -> assert false

let rec compile_module mlw_map ctxt mdl : mlw_map =
  let open T in
  match IdentM.find mdl.mdl_name mlw_map with
  | Compiled _ -> mlw_map
  | Uncompiled (Unary_module _) ->
    begin
      let mdl_qualid = mk_qualid [id_name mdl.mdl_name] in
      let intr_name = mdl.mdl_interface in
      let intr_str = id_name intr_name in
      let mlw_map, ctxt =
        match IdentM.find intr_name mlw_map with
        | Compiled (Unary ctxt, _) -> mlw_map, qualify_ctxt ctxt intr_str
        | Uncompiled (Unary_interface intr) ->
          let new_mlw = compile_interface mlw_map ctxt intr in
          begin match get_mlw_context new_mlw intr.intr_name with
            | Unary ctxt' -> new_mlw, qualify_ctxt ctxt' intr_str
            | _ -> assert false
          end
        | _ | exception Not_found -> assert false in
      let ctxt, decls, mlw_map = foldr (fun elt (ctxt, decls, mlw_map) ->
          let new_ctxt, decl, mlw =
            compile_module_elt mlw_map ctxt mdl_qualid elt in
          match decl with
          | None -> (new_ctxt, decls, mlw)
          | Some decl -> (new_ctxt, decl :: decls, mlw)
        ) (ctxt, [], mlw_map) mdl.mdl_elts in
      let import_intr = use_import [id_name intr_name] in
      let decls = standard_imports @ import_intr :: rev decls in
      let mlw_file = Ptree.Modules [mlw_name mdl.mdl_name, decls] in
      let update_fn = const (Some (Compiled (Unary ctxt, mlw_file))) in
      IdentM.update mdl.mdl_name update_fn mlw_map
    end
  | _ | exception Not_found ->
    failwith ("Unknown module: " ^ string_of_ident mdl.mdl_name)

and compile_module_elt mlw_map ctxt mdl_name elt
  : ctxt * Ptree.decl option * mlw_map =
  let open T in
  match elt with
  | Mdl_cdef _ | Mdl_datagroup _ -> ctxt, None, mlw_map
  | Mdl_mdef mdef ->
    let ctxt, decl = compile_meth_def ctxt mdef in
    let Method (mdecl, com) = mdef in
    let meth_name =
      if Ctbl.class_exists ctxt.ctbl mdecl.meth_name.node
      then mk_ctor_name mdecl.meth_name.node
      else mk_ident (id_name mdecl.meth_name.node) in
    (* NOTE: Cannot use add_ident here because of how constructors
       are handled.  If used in a New_class command, the name K is
       expected to map to mk_K; if used in a method call, the name
       K is expected to map to init_K. *)
    let ident_map =
      IdentM.add mdecl.meth_name.node (Id_other, mk_qualid [meth_name.id_str])
        ctxt.ident_map in
    let ctxt = {ctxt with ident_map} in
    ctxt, Some decl, mlw_map
  | Mdl_vdecl _ ->
    (* TIMEBOMB: This form is currently not allowed in source programs,
       but may be in future revisions. *)
    ctxt, None, mlw_map
  | Mdl_formula nf ->
    let decl = compile_named_formula ctxt nf in
    let name = id_name nf.formula_name.node in
    let ctxt = add_ident Id_other ctxt nf.formula_name.node name in
    ctxt, Some decl, mlw_map
  | Mdl_import import_direc ->
    let ctxt, decl, mlw_map = compile_module_import mlw_map ctxt import_direc in
    ctxt, Some decl, mlw_map
  | Mdl_extern ex -> add_extern_to_ctxt ctxt ex, None, mlw_map

and compile_module_import mlw_map ctxt import_direc
  : ctxt * Ptree.decl * mlw_map =
  let kind, import, as_name = import_direc in
  let import' = qualid_of_ident (mlw_name import) in
  let as_name' = Opt.map (mk_ident % id_name) as_name in
  let node = [import', as_name'] in
  let import_decl = Ptree.Duseimport (Loc.dummy_position, false, node) in
  match kind with
  | Itheory ->
    let import_fname = String.lowercase_ascii (id_name import) in
    let import_decl = use_export [import_fname; id_name import] in
    ctxt, import_decl, mlw_map
  | Iregular ->
    assert (IdentM.mem import mlw_map);
    match IdentM.find import mlw_map with
    | Compiled (Unary ctxt', _) ->
      let ctxt' = qualify_ctxt ctxt' (id_name import) in
      merge_ctxt ctxt ctxt', import_decl, mlw_map
    | Uncompiled (Unary_module mdef) ->
      let new_mlw = compile_module mlw_map ctxt mdef in
      assert (IdentM.mem import new_mlw);
      begin match get_mlw_context new_mlw import with
        | Unary ctxt' ->
          let ctxt' = qualify_ctxt ctxt' (id_name import) in
          merge_ctxt ctxt ctxt', import_decl, new_mlw
        | _ -> assert false
      end
    | _ | exception Not_found -> assert false


(* -------------------------------------------------------------------------- *)
(* Biprograms                                                                 *)
(* -------------------------------------------------------------------------- *)

let left_var  id = let name = id_name id in Id ("l_" ^ name)
let right_var id = let name = id_name id in Id ("r_" ^ name)

let rec compile_rformula bi_ctxt (rf: T.rformula) : Ptree.term =
  match rf with
  | Rbiequal (e1, e2) ->
    let e1' = term_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state e1 in
    let e2' = term_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state e2 in
    assert (e1.ty = e2.ty);
    begin match e1.ty, e2.ty with
      | Tclass k, Tclass _ -> id_ref_fn <*> [mk_qvar bi_ctxt.refperm; e1'; e2']
      | Tanyclass, _ -> id_ref_fn <*> [mk_qvar bi_ctxt.refperm; e1'; e2']
      | Trgn, _ -> id_rgn_fn <*> [mk_qvar bi_ctxt.refperm; e1'; e2']
      | _, _ -> e1' ==. e2'
    end
  | Rboth f ->
    let lf = term_of_formula bi_ctxt.left_ctxt bi_ctxt.left_state f in
    let rf = term_of_formula bi_ctxt.right_ctxt bi_ctxt.right_state f in
    lf ^&& rf
  | Rleft f -> term_of_formula bi_ctxt.left_ctxt bi_ctxt.left_state f
  | Rright f -> term_of_formula bi_ctxt.right_ctxt bi_ctxt.right_state f
  | Rnot rf -> let rf' = compile_rformula bi_ctxt rf in mk_term (Tnot rf')
  | Rconn (c, rf1, rf2) ->
    let rf1' = compile_rformula bi_ctxt rf1 in
    let rf2' = compile_rformula bi_ctxt rf2 in
    mk_term (Tbinop (rf1', dbinop_of_connective c, rf2'))
  | Rlet ((lid, lty, lb), (rid, rty, rb), rfrm) ->
    let lid_name = id_name (left_var lid.node) in
    let rid_name = id_name (right_var rid.node) in
    let lb' = term_of_let_bind bi_ctxt.left_ctxt bi_ctxt.left_state lb in
    let rb' = term_of_let_bind bi_ctxt.right_ctxt bi_ctxt.right_state rb in
    let lctxt = add_logic_ident bi_ctxt.left_ctxt lid.node lid_name in
    let rctxt = add_logic_ident bi_ctxt.right_ctxt rid.node rid_name in
    let bi_ctxt = {bi_ctxt with left_ctxt = lctxt; right_ctxt = rctxt} in
    let rfrm' = compile_rformula bi_ctxt rfrm in
    let inner = mk_term (Tlet (mk_ident rid_name, rb', rfrm')) in
    mk_term (Tlet (mk_ident lid_name, lb', inner))
  | Rquant (q, (lbinds, rbinds), rfrm) ->
    let lctxt = bi_ctxt.left_ctxt and rctxt = bi_ctxt.right_ctxt in
    let lstate = bi_ctxt.left_state and rstate = bi_ctxt.right_state in
    let q' = dquant_of_quantifier q in
    let lctxt', lbinds', lants = mk_binders ~prefix:"l_" lctxt lstate lbinds in
    let rctxt', rbinds', rants = mk_binders ~prefix:"r_" rctxt rstate rbinds in
    let bi_ctxt = {bi_ctxt with left_ctxt = lctxt'; right_ctxt = rctxt'} in
    let rfrm' = compile_rformula bi_ctxt rfrm in
    let inner = lants @ rants @ [rfrm'] in
    begin match q with
      | Forall -> mk_quant q' (lbinds' @ rbinds') (mk_implies inner)
      | Exists -> mk_quant q' (lbinds' @ rbinds') (mk_conjs inner)
    end
  | Rprimitive {name; left_args; right_args} ->
    assert (mem (mk_qualid [id_name name]) bi_ctxt.bipreds);
    let lctxt = bi_ctxt.left_ctxt and rctxt = bi_ctxt.right_ctxt in
    let largs = map (term_of_exp lctxt bi_ctxt.left_state) left_args in
    let rargs = map (term_of_exp rctxt bi_ctxt.right_state) right_args in
    let args = mk_qvar bi_ctxt.left_state
               :: mk_qvar bi_ctxt.right_state
               :: mk_qvar bi_ctxt.refperm
               :: largs @ rargs in
    mk_qualid [id_name name] <*> args
  | Ragree (g, f) ->
    (* Ragree (g, f) iff Agree(s,s',pi,rd G`f) and Agree(s',s,pi^-1,rd G`f)

       where
       Agree(s,s',pi,rd G`f) = Lagree(s,s',pi,rlocs(s,rd G`f))

       Lagree(s,s',pi,W) iff (forall x in W. s(x) ~(pi)~ s'(x))
                          /\ (forall (o.f) in W. o in dom(pi)
                                /\ s(o.f) ~(pi)~ s'(pi(o).f))

       rlocs(s,e) = {x | e contains rd x}
                  U {o.f | e contains some rd G`f with o in s(G), o <> null}
    *)
    let lg = term_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state g in
    let rg = term_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state g in
    let sl, sr = map_pair mk_qvar (bi_ctxt.left_state, bi_ctxt.right_state) in
    let pi = mk_qvar bi_ctxt.refperm in
    let agree_pred = match f with
      | {node = Id "any"; ty = Tdatagroup} ->
        qualid_of_ident Build_State.agreement_on_any
      | _ -> Build_State.agreement (lookup_field bi_ctxt.left_ctxt f.node) in
    let lagree = agree_pred <*> [sl; sr; pi; lg] in
    let ragree = agree_pred <*> [sr; sl; invert_refperm <*> [pi]; rg] in
    lagree ^&& ragree

let compile_named_rformula bi_ctxt nrf : Ptree.decl =
  let open T in
  let update_ctxt prefix ctxt params =
    let add_id id ctxt = add_ident Id_other ctxt id (prefix ^ id_name id) in
    foldr (fun (id,_) ctxt -> add_id id ctxt) ctxt params in
  let name = mk_ident (id_name nrf.T.biformula_name) in
  let body = nrf.body in
  let lstate_ident = ~. (fresh_name bi_ctxt.left_ctxt "l_s") in
  let rstate_ident = ~. (fresh_name bi_ctxt.right_ctxt "r_s") in
  let bi_ctxt = {bi_ctxt with left_state = qualid_of_ident lstate_ident;
                              right_state = qualid_of_ident rstate_ident } in
  let refperm_ident = gen_ident2 bi_ctxt "pi" in
  let refperm = qualid_of_ident refperm_ident in
  let bi_ctxt = {bi_ctxt with refperm} in
  match nrf.kind with
  | `Axiom | `Lemma as k ->
    let term =
      let+! lst, _ = bindvar (lstate_ident, state_type) in
      let+! rst, _ = bindvar (rstate_ident, state_type) in
      let+! pi,  _ = bindvar (refperm_ident, refperm_type) in
      return (compile_rformula bi_ctxt body) in
    let dprop_kind = if k = `Axiom then Decl.Paxiom else Decl.Plemma in
    Dprop (dprop_kind, name, build_term term)
  | `Predicate ->
    let lctxt, lstate = bi_ctxt.left_ctxt, bi_ctxt.left_state in
    let rctxt, rstate = bi_ctxt.right_ctxt, bi_ctxt.right_state in
    let lparams = map (fun (id,ty) -> (id.node,ty)) (fst nrf.biparams) in
    let rparams = map (fun (id,ty) -> (id.node,ty)) (snd nrf.biparams) in
    let lstate_param = mk_param lstate_ident false state_type in
    let rstate_param = mk_param rstate_ident false state_type in
    let refperm_param = mk_param refperm_ident false refperm_type in
    let lparams', lants =
      params_of_param_list lctxt ~prefix:"l_" lstate lparams in
    let rparams', rants =
      params_of_param_list rctxt ~prefix:"r_" rstate rparams in
    let left_ctxt  = update_ctxt "l_" bi_ctxt.left_ctxt lparams in
    let right_ctxt = update_ctxt "r_" bi_ctxt.right_ctxt rparams in
    let bi_ctxt = { bi_ctxt with left_ctxt ; right_ctxt } in
    let qname = qualid_of_ident name in
    let bi_ctxt = { bi_ctxt with bipreds = qname :: bi_ctxt.bipreds } in
    let body = compile_rformula bi_ctxt body in
    let ext_body = mk_implies (lants @ rants @ [body]) in
    let params =
      lstate_param
      :: rstate_param
      :: refperm_param
      :: lparams' @ rparams' in
    let ldecl =
      Ptree.{ ld_loc = Loc.dummy_position;
              ld_ident = name;
              ld_params = params;
              ld_type = None;
              ld_def = Some ext_body } in
    Dlogic [ldecl]

let rec split_rconjuncts (rfrm: T.rformula) : T.rformula list =
  match rfrm with
  | Rconn (Conj, rf1, rf2) -> split_rconjuncts rf1 @ split_rconjuncts rf2
  | _ -> [rfrm]

let rec compile_bicommand bi_ctxt (cc: T.bicommand) : Ptree.expr =
  let { left_state = lstate; right_state = rstate } = bi_ctxt in
  match cc with
  | Bisplit (c1, c2) ->
    let c1 = expr_of_command bi_ctxt.left_ctxt lstate c1 in
    let c2 = expr_of_command bi_ctxt.right_ctxt rstate c2 in
    mk_expr (Esequence (c1, c2))
  | Bisync (Call (xopt, {node=Id meth; ty=meth_ty}, args) as ac)
    when IdentM.mem (Id meth) bi_ctxt.bimethods ->
    (* FIXME: may have to lookup method in ctxt *)
    let args = map (fun e -> T.Evar e -: e.ty) args in
    let largs = map (expr_of_exp bi_ctxt.left_ctxt lstate) args in
    let rargs = map (expr_of_exp bi_ctxt.right_ctxt rstate) args in
    let meth_name = fst (IdentM.find (Id meth) bi_ctxt.bimethods) in
    (* let meth_name = mk_qualid [meth] in *)
    let args = mk_qevar lstate
               :: mk_qevar rstate
               :: mk_qevar bi_ctxt.refperm
               :: largs @ rargs in
    let call = mk_eapp meth_name args in
    let msg =
      let () = pp_atomic_command_special Format.str_formatter ac in
      Format.flush_str_formatter () in
    begin match xopt with
      | Some x ->
        let res = meth ^ "_res" in
        let lres = gen_ident2 bi_ctxt ("l_" ^ res) in
        let rres = gen_ident2 bi_ctxt ("r_" ^ res) in
        let lexp = mk_evar lres in
        let rexp = mk_evar rres in
        let lpat = mk_pat (Pvar (gen_ident2 bi_ctxt lres.id_str)) in
        let rpat = mk_pat (Pvar (gen_ident2 bi_ctxt rres.id_str)) in
        let pat  = mk_pat (Ptuple [lpat; rpat]) in
        let lupd = update_id ~msg bi_ctxt.left_ctxt lstate x.node lexp in
        let rupd = update_id ~msg bi_ctxt.right_ctxt rstate x.node rexp in
        let upd  = mk_expr (Esequence (lupd, rupd)) in
        mk_expr (Ematch (call, [pat, upd], []))
      | None ->
        let pat = mk_pat Pwild in
        let unit = mk_expr (Etuple []) in
        mk_expr (Ematch (explain_expr call msg, [pat, unit], []))
    end
  | Bisync ac ->
    let ac1 = expr_of_atomic_command bi_ctxt.left_ctxt lstate ac in
    let ac2 = expr_of_atomic_command bi_ctxt.right_ctxt rstate ac in
    mk_expr (Esequence (ac1, ac2))
  | Bivardecl ((lid, lmodif, lty), (rid, rmodif, rty), inner) ->
    let lid_name = id_name (left_var lid.node) in
    let rid_name = id_name (right_var rid.node) in
    let lid_val = default_value bi_ctxt.left_ctxt lty in
    let lid_val = mk_expr (Eapply (mk_expr Eref, lid_val)) in
    let rid_val = default_value bi_ctxt.right_ctxt rty in
    let rid_val = mk_expr (Eapply (mk_expr Eref, rid_val)) in
    let lid_gho = match lmodif with Some Ghost -> true | _ -> lty = Trgn in
    let rid_gho = match rmodif with Some Ghost -> true | _ -> rty = Trgn in
    let left_ctxt  = add_local_ident lty bi_ctxt.left_ctxt lid.node lid_name in
    let right_ctxt = add_local_ident rty bi_ctxt.right_ctxt rid.node rid_name in
    let bi_ctxt = { bi_ctxt with left_ctxt ; right_ctxt } in
    let cc = compile_bicommand bi_ctxt inner in
    let lid, rid = mk_ident lid_name, mk_ident rid_name in
    let inner = mk_expr (Elet (rid, rid_gho, Expr.RKnone, rid_val, cc)) in
    mk_expr (Elet (lid, lid_gho, Expr.RKnone, lid_val, inner))
  | Biseq (cc1, cc2) ->
    let cc1 = compile_bicommand bi_ctxt cc1 in
    let cc2 = compile_bicommand bi_ctxt cc2 in
    mk_expr (Esequence (cc1, cc2))
  | Biassert rfrm ->
    let rfrm = compile_rformula bi_ctxt rfrm in
    mk_expr (Eassert (Expr.Assert, rfrm))
  | Biassume rfrm ->
    let rfrm = compile_rformula bi_ctxt rfrm in
    mk_expr (Eassert (Expr.Assume, rfrm))
  | Biupdate (x, y) ->          (* Update the refperm *)
    let var_x = T.Evar x -: x.ty and var_y = T.Evar y -: y.ty in
    let x' = expr_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state var_x in
    let y' = expr_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state var_y in
    let rp = mk_qevar bi_ctxt.refperm in
    mk_expr (Eidapp (update_refperm, [rp; x'; y']))
  | Biif (lg, rg, cc1, cc2) ->
    let lgterm = term_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state lg in
    let rgterm = term_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state rg in
    let guard_cond = mk_expr (Eassert (Expr.Assert, lgterm ==. rgterm)) in
    let guard_cond = explain_expr guard_cond "guard agreement" in
    let guard = expr_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state lg in
    let conseq = compile_bicommand bi_ctxt cc1 in
    let alter = compile_bicommand bi_ctxt cc2 in
    let if_expr = mk_expr (Eif (guard, conseq, alter)) in
    mk_expr (Esequence (guard_cond, if_expr))
  | Biwhile (lg, rg, (Rleft Ffalse, Rright Ffalse), rinv, cc) ->
    compile_lockstep_biwhile bi_ctxt lg rg rinv cc
  | Biwhile (lg, rg, (lf, rf), rinv, cc) ->
    compile_biwhile bi_ctxt lg rg lf rf rinv cc

(* compile_lockstep_biwhile Ctx lguard rguard REL_inv CC =

     while (lguard) do
       invariant { lguard = rguard /\ REL_inv }
       CC
     end
*)
and compile_lockstep_biwhile bi_ctxt lg rg rinv cc =
  let lg' = term_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state lg in
  let rg' = term_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state rg in
  let rinvs = map (compile_rformula bi_ctxt) (split_rconjuncts rinv) in
  let rinvs = Build_State.ok_refperm
      bi_ctxt.left_state
      bi_ctxt.right_state
      bi_ctxt.refperm :: rinvs in
  let guard = expr_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state lg in
  let rbody = compile_bicommand bi_ctxt cc in
  let lockstep = explain_term (lg' ==. rg') "lockstep" in
  mk_expr (Ewhile (guard, lockstep :: rinvs, [], rbody))

(* compile_biwhile Ctx lguard rguard lalign ralign REL_inv CC =

     while (lguard || rguard) do
       invariant { <<alignment condition>> /\ okRefperm ... /\ REL_inv }
       <<inner>>
     done;

   where
   alignment condition is
     (lguard /\ lalign) \/
     (lguard /\ rguard) \/
     (not lguard /\ not rguard) \/
     (rguard /\ ralign)

   and inner is
     if (lguard && lalign) then CC<- else
     if (rguard && ralign) then CC-> else CC

   Note: if alignment condition is false, then while E|E'.P|P' BB end |==> Fault
   Further, if the alignment condition holds, then
     not ((lguard = true  /\ rguard = false /\ not lalign) \/
          (lguard = false /\ rguard = true  /\ not ralign))
   holds.
*)
and compile_biwhile bi_ctxt lg rg lf rf rinv cc =
  let ccl = T.projl cc and ccr = T.projr cc in
  let lg_term = term_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state lg in
  let rg_term = term_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state rg in
  let lg_exp = expr_of_exp bi_ctxt.left_ctxt bi_ctxt.left_state lg in
  let rg_exp = expr_of_exp bi_ctxt.right_ctxt bi_ctxt.right_state rg in
  let lf_term = compile_rformula bi_ctxt lf in
  let rf_term = compile_rformula bi_ctxt rf in
  let lf_exp = expr_of_rel_formula bi_ctxt lf in
  let rf_exp = expr_of_rel_formula bi_ctxt rf in
  let align_cond =
    let left_step_cond = lg_term ^&& lf_term in
    let rght_step_cond = rg_term ^&& rf_term in
    let lockstep_cond = lg_term ^&& rg_term in
    let on_end = (mk_term (Tnot lg_term)) ^&& (mk_term (Tnot (rg_term))) in
    let cond = left_step_cond ^|| rght_step_cond ^|| lockstep_cond ^|| on_end in
    explain_term cond "alignment condition" in
  let rinvs' = map (compile_rformula bi_ctxt) (split_rconjuncts rinv) in
  let rinvs' = rinvs' @ [align_cond] in
  let rinvs' = Build_State.ok_refperm
      bi_ctxt.left_state
      bi_ctxt.right_state
      bi_ctxt.refperm :: rinvs' in
  let while_guard = lg_exp ^| rg_exp in
  let bwhl_guard = lg_exp ^& lf_exp in
  let bwhl_guard = explain_expr bwhl_guard "Left step" in
  let bwhr_guard = rg_exp ^& rf_exp in
  let bwhr_guard = explain_expr bwhr_guard "Right step" in
  let bwhl_body = expr_of_command bi_ctxt.left_ctxt bi_ctxt.left_state ccl in
  let bwhr_body = expr_of_command bi_ctxt.right_ctxt bi_ctxt.right_state ccr in
  let bwhtt_body = compile_bicommand bi_ctxt cc in
  let bwhr_if = mk_expr (Eif (bwhr_guard, bwhr_body, bwhtt_body)) in
  let bwhl_if = mk_expr (Eif (bwhl_guard, bwhl_body, bwhr_if)) in
  mk_expr (Ewhile (while_guard, rinvs', [], bwhl_if))

and expr_of_formula ctxt state f : Ptree.expr =
  let open T in
  match f with
  | Ftrue -> expr_of_const_exp (Ebool true -: Tbool)
  | Ffalse -> expr_of_const_exp (Ebool false -: Tbool)
  | Fnot f -> mk_expr (Enot (expr_of_formula ctxt state f))
  | Fexp e -> expr_of_exp ctxt state e
  | Fpointsto (x, f, e) ->
    let x_f = st_load ctxt state (x,f) in
    let e' = expr_of_exp ctxt state e in
    expr_of_binop Equal (x_f, f.ty) (e', e.ty)
  | Fconn (c, f1, f2) ->
    let f1' = expr_of_formula ctxt state f1 in
    let f2' = expr_of_formula ctxt state f2 in
    begin match c with
      | Conj -> mk_expr (Eand (f1', f2'))
      | Disj -> mk_expr (Eor (f1', f2'))
      | Imp -> mk_expr (Eor (mk_expr (Enot f1'), f2'))
      | Iff -> expr_of_binop Equal (f1', Tbool) (f2', Tbool)
    end
  | f -> mk_expr (Epure (term_of_formula ctxt state f))

(* Try and compile an rformula to a Why3 expression.

   Simple rformulas such as <| x.f = true <] can be compiled to the
   expression ``x.f''.  For more complicated cases, such as when the
   rformula contains quantifiers, they may only be compiled to ``pure
   { ... }''.  This isn't ideal since it may require annotating the
   Why3 function as ghost (NOT done by our compiler).

   TODO: More heuristics.

*)
and expr_of_rel_formula bi_ctxt rf : Ptree.expr =
  let open T in
  match rf with
  | Rleft f -> expr_of_formula bi_ctxt.left_ctxt bi_ctxt.left_state f
  | Rright f -> expr_of_formula bi_ctxt.right_ctxt bi_ctxt.right_state f
  | Rconn (c, rf1, rf2) ->
    let rf1' = expr_of_rel_formula bi_ctxt rf1 in
    let rf2' = expr_of_rel_formula bi_ctxt rf2 in
    begin match c with
      | Conj -> mk_expr (Eand (rf1', rf2'))
      | Disj -> mk_expr (Eor (rf1', rf2'))
      | Imp -> mk_expr (Eor (mk_expr (Enot rf1'), rf2'))
      | Iff -> expr_of_binop Equal (rf1', Tbool) (rf2', Tbool)
    end
  | Rboth f ->
    let fl = expr_of_formula bi_ctxt.left_ctxt bi_ctxt.left_state f in
    let fr = expr_of_formula bi_ctxt.right_ctxt bi_ctxt.right_state f in
    mk_expr (Eand (fl, fr))
  | Rnot f -> mk_expr (Enot (expr_of_rel_formula bi_ctxt f))
  | _ -> mk_expr (Epure (compile_rformula bi_ctxt rf))

let left_effects (bispec: T.bispec) : T.effect =
  concat_filter_map (function
      | T.Bieffects (e, _) -> Some e
      | _ -> None
    ) bispec

let right_effects (bispec: T.bispec) : T.effect =
  concat_filter_map (function
      | T.Bieffects (_, e) -> Some e
      | _ -> None
    ) bispec

let rec compile_bispec bi_ctxt bispec =
  let open T in
  let open List in
  let rec get_spec pre post effs = function
    | [] -> (pre, post, effs)
    | Biprecond rf :: rest -> get_spec (rf::pre) post effs rest
    | Bipostcond rf :: rest -> get_spec pre (rf::post) effs rest
    | Bieffects (e,e') :: rest -> get_spec pre post ((e,e') :: effs) rest in
  let pre, post, effs = get_spec [] [] [] (rev bispec) in
  let pre, post, effs = rev pre, rev post, rev effs in
  let effs = map_pair flatten (unzip effs) in
  let leffs, reffs = map_pair Normalize_effects.normalize_effect effs in
  let pre = map (compile_rformula bi_ctxt) pre in
  let post = map (compile_bispec_post bi_ctxt) post in
  let lctxt, lstate = bi_ctxt.left_ctxt, bi_ctxt.left_state in
  let rctxt, rstate = bi_ctxt.right_ctxt, bi_ctxt.right_state in
  let ok_refperm = Build_State.ok_refperm lstate rstate bi_ctxt.refperm in
  let pre = ok_refperm :: pre and post = mk_ensures ok_refperm :: post in
  let lconds = mk_wr_frame_condition lctxt lstate leffs in
  let rconds = mk_wr_frame_condition rctxt rstate reffs in
  let lwrites = compile_writes lctxt lstate leffs in
  let rwrites = compile_writes rctxt rstate reffs in
  let writes = lwrites @ rwrites in
  mk_spec pre ((map mk_ensures (lconds @ rconds)) @ post) [] writes

and compile_bispec_post bi_ctxt post =
  let fvs = T.free_vars_rformula post in
  let result = Id "result" in
  let post' = compile_rformula bi_ctxt post in
  let post' =
    if T.IdS.mem result fvs then begin
      let l_result = mk_ident (id_name (left_var result)) in
      let r_result = mk_ident (id_name (right_var result)) in
      let l_respat = pat_var l_result and r_respat = pat_var r_result in
      let respat = mk_pat (Ptuple [l_respat; r_respat]) in
      mk_term (Tcase (~*(~.(id_name result)), [respat, post']))
    end else post' in
  mk_ensures post'

let prefix_meth_param prefix meth_param =
  let open T in
  let name = Id (prefix ^ id_name meth_param.param_name.node) in
  {meth_param with param_name = name -: meth_param.param_name.ty}


let extend_bimeth_spec res_ty res_non_null bispec =
  let open T in

  let res_is_unit_cond =
    if res_ty = (Tunit,Tunit) then
      let res_var = Evar (Id "result" -: Tunit) -: Tunit in
      let unit_exp = Econst (Eunit -: Tunit) -: Tunit in
      let eq_exp = Ebinop (Ast.Equal, res_var, unit_exp) -: Tbool in
      [Bipostcond (Rboth (Fexp eq_exp))]
    else [] in

  let res_non_null_cond =
    if res_non_null = (true,true) && fst res_ty = snd res_ty then
      let res_ty = fst res_ty in
      let res_var = Evar (Id "result" -: res_ty) -: res_ty in
      let null_exp = Econst (Enull -: res_ty) -: res_ty in
      let eq_exp = Ebinop (Ast.Equal, res_var, null_exp) -: Tbool in
      [Bipostcond (Rboth (Fnot (Fexp eq_exp)))]
    else [] in

  res_is_unit_cond @ res_non_null_cond @ bispec

let bimeth_spec_extra_post bi_ctxt res_ty =
  let result = Id "result" in
  let lres_ty, rres_ty = res_ty in
  let lcond = match lres_ty with
    | T.Tclass k ->
      let cpred = Build_State.has_class_type_pred k in
      let l_result = mk_ident (id_name (left_var result)) in
      let l_respat = pat_var l_result in
      let respat = mk_pat (Ptuple [l_respat; mk_pat Pwild]) in
      let inner = cpred <*> [mk_qvar bi_ctxt.left_state; ~* l_result] in
      let cond = mk_term (Tcase (~*(~.(id_name result)), [respat, inner])) in
      [mk_ensures cond]
    | _ -> [] in
  let rcond = match rres_ty with
    | T.Tclass k ->
      let cpred = Build_State.has_class_type_pred k in
      let r_result = mk_ident (id_name (right_var result)) in
      let r_respat = pat_var r_result in
      let respat = mk_pat (Ptuple [mk_pat Pwild; r_respat]) in
      let inner = cpred <*> [mk_qvar bi_ctxt.right_state; ~* r_result] in
      let cond = mk_term (Tcase (~*(~.(id_name result)), [respat, inner])) in
      [mk_ensures cond]
    | _ -> [] in
  lcond @ rcond

let rec compile_bimethod bi_ctxt bimethod : bi_ctxt * Ptree.decl =
  let open T in
  let Bimethod (bimdecl, ccopt) = bimethod in

  let add_params prefix ctxt params =
    foldr (fun pinfo ctxt ->
        let id = pinfo.param_name.node in
        add_ident Id_other ctxt id (prefix ^ id_name id)
      ) ctxt params in

  let meth_name =
    let name = bimdecl.bimeth_name in
    if Ctbl.class_exists bi_ctxt.left_ctxt.ctbl name
    && Ctbl.class_exists bi_ctxt.right_ctxt.ctbl name
    then mk_ctor_name name
    else mk_ident (id_name name) in

  let lret_ty, rret_ty = map_pair pty_of_ty bimdecl.result_ty in
  let ret_ty = mk_pair_ty lret_ty rret_ty in
  let lresult = gen_ident2 bi_ctxt "l_result" in
  let rresult = gen_ident2 bi_ctxt "r_result" in
  let result = Id "result" in
  let lctxt = add_ident Id_other bi_ctxt.left_ctxt result lresult.id_str in
  let rctxt = add_ident Id_other bi_ctxt.right_ctxt result rresult.id_str in
  let bi_ctxt = {bi_ctxt with left_ctxt = lctxt; right_ctxt = rctxt} in
  let lstate = ~. (fresh_name bi_ctxt.left_ctxt "l_s") in
  let rstate = ~. (fresh_name bi_ctxt.right_ctxt "r_s") in
  let left_state, right_state = map_pair qualid_of_ident (lstate, rstate) in
  let bi_ctxt = {bi_ctxt with left_state; right_state} in
  let refperm_id = gen_ident2 bi_ctxt "pi" in
  let refperm = qualid_of_ident refperm_id in
  let bi_ctxt = {bi_ctxt with refperm} in
  let lps, rps = bimdecl.bimeth_left_params, bimdecl.bimeth_right_params in
  let lparams, lext = params_of_param_info_list ~prefix:"l_" left_state lps in
  let rparams, rext = params_of_param_info_list ~prefix:"r_" right_state rps in
  let extra_pre = lext @ rext in
  let left_ctxt  = add_params "l_" bi_ctxt.left_ctxt lps in
  let right_ctxt = add_params "r_" bi_ctxt.right_ctxt rps in
  let bi_ctxt = {bi_ctxt with left_ctxt; right_ctxt} in

  let bispec =
    let res_ty = bimdecl.result_ty in
    let res_ty_non_null = bimdecl.result_ty_is_non_null in
    extend_bimeth_spec res_ty res_ty_non_null bimdecl.bimeth_spec in
  let bimdecl = {bimdecl with bimeth_spec = bispec} in

  let lst_param = mk_param lstate false state_type in
  let rst_param = mk_param rstate false state_type in
  let pi_param  = mk_param refperm_id false refperm_type in
  let params = lst_param :: rst_param :: pi_param :: lparams @ rparams in

  match ccopt with
  | None ->
    let bispec = compile_bispec bi_ctxt bimdecl.bimeth_spec in
    let bispec = {bispec with sp_pre = extra_pre @ bispec.sp_pre } in
    let e = mk_abstract_expr params ret_ty bispec in
    let meth_qualid = qualid_of_ident meth_name in
    let wrs = specified_writes bispec in
    let bimethods =
      IdentM.add bimdecl.bimeth_name (meth_qualid, wrs) bi_ctxt.bimethods in
    (* let bimethods = QualidM.add meth_qualid wrs bi_ctxt.bimethods in *)
    let bi_ctxt = {bi_ctxt with bimethods} in
    bi_ctxt, Dlet (meth_name, false, Expr.RKnone, e)
  | Some cc ->
    let ccl = projl cc and ccr = projr cc in
    let lctxt = bi_ctxt.left_ctxt and rctxt = bi_ctxt.right_ctxt in
    let lalloc'd = IdentS.elements (classes_instantiated lctxt ccl) in
    let ralloc'd = IdentS.elements (classes_instantiated rctxt ccr) in
    let lctxt = bi_ctxt.left_ctxt and rctxt = bi_ctxt.right_ctxt in
    let lextra_wrs = concat_map (fresh_obj_wrs lctxt.ctbl) lalloc'd in
    let rextra_wrs = concat_map (fresh_obj_wrs rctxt.ctbl) ralloc'd in

    let bispec = T.Bieffects (lextra_wrs, rextra_wrs) :: bimdecl.bimeth_spec in
    let bispec = compile_bispec bi_ctxt bispec in
    let bispec = {bispec with sp_pre = extra_pre @ bispec.sp_pre } in
    let extra_post = bimeth_spec_extra_post bi_ctxt bimdecl.result_ty in
    let bispec = {bispec with sp_post = extra_post @ bispec.sp_post } in

    let lres_ity, rres_ity = bimdecl.result_ty in
    let lres, rres = lresult.id_str, rresult.id_str in
    let lctxt = add_local_ident lres_ity bi_ctxt.left_ctxt result lres in
    let rctxt = add_local_ident rres_ity bi_ctxt.right_ctxt result rres in

    let bi_ctxt = {bi_ctxt with left_ctxt=lctxt; right_ctxt=rctxt} in
    let com_ctx = build_bimethod_ctx bi_ctxt (lps, rps) in
    let body_uc = com_ctx cc in

    let lval = default_value bi_ctxt.left_ctxt lres_ity in
    let rval = default_value bi_ctxt.right_ctxt rres_ity in
    let lval = mk_expr (Eapply (mk_expr Eref, lval)) in
    let rval = mk_expr (Eapply (mk_expr Eref, rval)) in
    let body' = mk_expr (Elet (rresult, false, Expr.RKnone, lval, body_uc)) in
    let body = mk_expr (Elet (lresult, false, Expr.RKnone, rval, body')) in
    let body = mk_expr (Elabel (init_label, body)) in

    let wrttn = fields_written_bimethod bi_ctxt body in
    (* always include writes to the refperm in spec_writes.  Will get removed if
       updateRefperm is not called in the method body. *)
    let spec_writes = QualidS.add bi_ctxt.refperm (specified_writes bispec) in
    let lflds = fields_of_fresh_obj_wrs lctxt bi_ctxt.left_state lextra_wrs in
    let rflds = fields_of_fresh_obj_wrs rctxt bi_ctxt.right_state rextra_wrs in
    let lflds =
      if lalloc'd <> [] && alloc_in_writes (left_effects bimdecl.bimeth_spec)
      then QualidS.add (bi_ctxt.left_state %. st_alloct_field) lflds
      else lflds in
    let rflds =
      if ralloc'd <> [] && alloc_in_writes (right_effects bimdecl.bimeth_spec)
      then QualidS.add (bi_ctxt.right_state %. st_alloct_field) rflds
      else rflds in
    let extra_flds = QualidS.union lflds rflds in
    let wrs = QualidS.(union (inter wrttn spec_writes) extra_flds) in
    let sp_wrs = terms_of_fields_written wrs in
    let bispec = {bispec with sp_writes = sp_wrs} in
    (* Build Why3 function *)
    let binders = map binder_of_param params in
    let pat = mk_pat Pwild in
    let ret = Some ret_ty in
    let mask = Ity.MaskVisible in
    let fundef = mk_expr (Efun (binders, ret, pat, mask, bispec, body)) in

    let meth_qualid = qualid_of_ident meth_name in
    let bimethods =
      IdentM.add bimdecl.bimeth_name (meth_qualid, wrs) bi_ctxt.bimethods in
    (* let bimethods = QualidM.add meth_qualid wrs bi_ctxt.bimethods in *)
    let bi_ctxt = {bi_ctxt with bimethods} in

    bi_ctxt, Dlet (meth_name, false, Expr.RKnone, fundef)

and fields_written_bimethod bi_ctxt com : QualidS.t =
  let open QualidS in
  match com.Ptree.expr_desc with
  | Eassign [{expr_desc = Eident f; _}, None, _] -> singleton f
  | Esequence (e1,e2) | Eif (_,e1,e2) ->
    let e1wrs = fields_written_bimethod bi_ctxt e1 in
    let e2wrs = fields_written_bimethod bi_ctxt e2 in
    union e1wrs e2wrs
  | Elet (_,_,_,_,e)
  | Ewhile (_,_,_,e) -> fields_written_bimethod bi_ctxt e
  | Eattr (_,e) | Elabel (_,e) -> fields_written_bimethod bi_ctxt e
  | Eidapp (fn_name, _) when fn_name = update_refperm ->
    singleton bi_ctxt.refperm
  | Eidapp (fn_name, _) ->
    let bindings = IdentM.bindings bi_ctxt.bimethods in
    let bimeth_wrs = List.map snd bindings in
    begin
      try assoc fn_name bimeth_wrs
      with Not_found ->
        (* FIXME: fields_written should not return qualids that contain the
           state param.  The state params name may change.  Below, we handle the
           case where the unary state param is "s" but the biprog state params
           are "l_s" and "r_s".
        *)
        let lstate = (ident_of_qualid bi_ctxt.left_state).id_str in
        let rstate = (ident_of_qualid bi_ctxt.right_state).id_str in
        let lwrs = fields_written bi_ctxt.left_ctxt com in
        let lwrs = QualidS.map (fun k -> match string_list_of_qualid k with
            | _::ks -> mk_qualid (lstate :: ks)
            | _ -> k
          ) lwrs in
        let rwrs = fields_written bi_ctxt.right_ctxt com in
        let rwrs = QualidS.map (fun k -> match string_list_of_qualid k with
            | _::ks -> mk_qualid (rstate :: ks)
            | _ -> k
          ) rwrs in
        union lwrs rwrs
    end
  | Ematch (scrutinee, pat_list, _) ->
    let exprs = List.map snd pat_list in
    let expr_wrs = List.map (fields_written_bimethod bi_ctxt) exprs in
    let s_wrs = fields_written_bimethod bi_ctxt scrutinee in
    foldr union s_wrs expr_wrs
  | _ ->
    let lstate = (ident_of_qualid bi_ctxt.left_state).id_str in
    let rstate = (ident_of_qualid bi_ctxt.right_state).id_str in
    let lwrs = fields_written bi_ctxt.left_ctxt com in
    let lwrs = QualidS.map (fun k -> match string_list_of_qualid k with
        | _::ks -> mk_qualid (lstate :: ks)
        | _ -> k
      ) lwrs in
    let rwrs = fields_written bi_ctxt.right_ctxt com in
    let rwrs = QualidS.map (fun k -> match string_list_of_qualid k with
        | _::ks -> mk_qualid (rstate :: ks)
        | _ -> k
      ) rwrs in
    union lwrs rwrs

and build_bimethod_ctx bi_ctxt (lparams, rparams) cc =
  let open T in
  let lstate, rstate = bi_ctxt.left_state, bi_ctxt.right_state in

  let param_name = function
    | `L p -> id_name (left_var p.param_name.node)
    | `R p -> id_name (right_var p.param_name.node) in

  let rec add_to_expr cc fin : Ptree.expr =
    match cc.Ptree.expr_desc with
    | Elet (id, gho, knd, value, body) ->
      mk_expr (Elet (id, gho, knd, value, add_to_expr body fin))
    | Esequence (e1, e2) ->
      mk_expr (Esequence (e1, add_to_expr e2 fin))
    | _ -> mk_expr (Esequence (cc, fin)) in

  let rec aux bi_ctxt = function
    | [] ->
      (* lres should be l_result and rres should be r_result *)
      let lres = lookup_id bi_ctxt.left_ctxt lstate (Id "result") in
      let rres = lookup_id bi_ctxt.right_ctxt rstate (Id "result") in
      let ret = mk_expr (Etuple [lres; rres]) in
      add_to_expr (compile_bicommand bi_ctxt cc) ret
    | p :: ps ->
      let name = mk_ident (param_name p) in
      let copy = mk_expr (Eapply (mk_expr Eref, mk_evar name)) in
      let bi_ctxt = match p with
        | `L p ->
          let ctxt = bi_ctxt.left_ctxt in
          let p_ity = p.param_ty in
          let ctxt = add_local_ident p_ity ctxt p.param_name.node name.id_str in
          {bi_ctxt with left_ctxt = ctxt}
        | `R p ->
          let ctxt = bi_ctxt.right_ctxt in
          let p_ity = p.param_ty in
          let ctxt = add_local_ident p_ity ctxt p.param_name.node name.id_str in
          {bi_ctxt with right_ctxt = ctxt} in
      mk_expr (Elet (name, false, Expr.RKnone, copy, aux bi_ctxt ps)) in

  let lparams = map (fun e -> `L e) lparams in
  let rparams = map (fun e -> `R e) rparams in
  aux bi_ctxt (lparams @ rparams)

let rec compile_bimodule mlw_map bi_ctxt bimdl : mlw_map =
  let open T in
  let lmdl = bimdl.bimdl_left_impl and rmdl = bimdl.bimdl_right_impl in
  let lmlw_map, lctxt =
    match IdentM.find lmdl mlw_map with
    | Compiled (Unary ctxt, _) -> mlw_map, ctxt
    | Uncompiled (Unary_module lmdl_def) ->
      (* FIXME: This case should never occur, given the sequence in
         which modules are compiled (using dependency info). *)
      let new_mlw = compile_module mlw_map bi_ctxt.left_ctxt lmdl_def in
      new_mlw, get_unary_ctxt (get_mlw_context new_mlw lmdl_def.mdl_name)
    | _ | exception Not_found -> assert false in
  let rmlw_map, rctxt =
    match IdentM.find rmdl lmlw_map with
    | Compiled (Unary ctxt, _) -> lmlw_map, ctxt
    | Uncompiled (Unary_module rmdl_def) ->
      let new_mlw = compile_module lmlw_map bi_ctxt.right_ctxt rmdl_def in
      new_mlw, get_unary_ctxt (get_mlw_context new_mlw rmdl_def.mdl_name)
    | _ | exception Not_found -> assert false in
  let lctxt = qualify_ctxt lctxt (id_name lmdl) in
  let rctxt = qualify_ctxt rctxt (id_name rmdl) in
  let bi_ctxt = {bi_ctxt with left_ctxt = lctxt; right_ctxt = rctxt} in
  let bi_ctxt, decls, mlw_map = foldr (fun elt (ctxt, decls, mlw_map) ->
      let new_ctxt, decl, mlw = compile_bimodule_elt mlw_map ctxt elt in
      match decl with
      | None -> (new_ctxt, decls, mlw)
      | Some decl -> (new_ctxt, decl :: decls, mlw)
    ) (bi_ctxt, [], mlw_map) bimdl.bimdl_elts in
  let import_lmdl = use_import [id_name lmdl] in
  let import_rmdl = use_import [id_name rmdl] in
  let imports = standard_imports @ [import_lmdl; import_rmdl] in
  let decls = imports @ rev decls in
  let mlw_file = Ptree.Modules [mlw_name bimdl.bimdl_name, decls] in
  let update_fn = const (Some (Compiled (Relational bi_ctxt, mlw_file))) in
  IdentM.update bimdl.bimdl_name update_fn mlw_map

and compile_bimodule_elt mlw_map bi_ctxt elt
  : bi_ctxt * Ptree.decl option * mlw_map =
  let open T in
  match elt with
  | Bimdl_formula nf ->
    let decl = compile_named_rformula bi_ctxt nf in
    let name = id_name nf.biformula_name in
    let bi_ctxt = {bi_ctxt with bipreds = mk_qualid [name]::bi_ctxt.bipreds} in
    bi_ctxt, Some decl, mlw_map
  | Bimdl_mdef mdef ->
    let Bimethod (bimdecl, _) = mdef in
    let bi_ctxt, decl = compile_bimethod bi_ctxt mdef in
    bi_ctxt, Some decl, mlw_map
  | Bimdl_extern ext -> bi_ctxt, None, mlw_map
  | Bimdl_import idecl -> compile_bimodule_import mlw_map bi_ctxt idecl

and compile_bimodule_import mlw_map bi_ctxt import_direc
  : bi_ctxt * Ptree.decl option * mlw_map =
  let kind, import, as_name = import_direc in
  let import' = qualid_of_ident (mlw_name import) in
  let as_name = Opt.map (mk_ident % id_name) as_name in
  let node = [import', as_name] in
  let import_decl = Some (Ptree.Duseimport (Loc.dummy_position, false, node)) in
  match kind with
  | Itheory ->
    let import_fname = String.lowercase_ascii (id_name import) in
    let import_decl = Some (use_export [import_fname; id_name import]) in
    bi_ctxt, import_decl, mlw_map
  | Iregular ->
    assert (IdentM.mem import mlw_map);
    match IdentM.find import mlw_map with
    | Compiled (Relational bi_ctxt', _) ->
      let bi_ctxt' = qualify_bi_ctxt bi_ctxt' (id_name import) in
      merge_bi_ctxt bi_ctxt bi_ctxt', import_decl, mlw_map
    | Uncompiled _ | _ | exception Not_found -> assert false


(* -------------------------------------------------------------------------- *)
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

let compile_penv ctxt penv deps =
  let ini_mlw_map = mlw_map_of_penv penv in
  let modules = foldr (fun mdlname acc ->
      (mdlname, IdentM.find mdlname ini_mlw_map) :: acc
    ) [] deps in
  if !trans_debug then begin
    let open Printf in
    fprintf stderr "Compilation sequence: ";
    List.iter (fun (k,_) -> fprintf stderr "%s " (string_of_ident k)) modules;
    fprintf stderr "\n";
  end;
  let loop name frag mlw_map = match frag with
    | Uncompiled (T.Unary_interface i) ->
      let ctxt = {ctxt with current_mdl = Some name} in
      compile_interface mlw_map ctxt i
    | Uncompiled (T.Unary_module m) ->
      let ctxt = {ctxt with current_mdl = Some name} in
      compile_module mlw_map ctxt m
    | Uncompiled (T.Relation_module m) ->
      let left_mdl, right_mdl = m.bimdl_left_impl, m.bimdl_right_impl in
      let current_bimdl = Some (left_mdl, right_mdl, m.bimdl_name) in
      let bi_ctxt = {ini_bi_ctxt with current_bimdl} in
      compile_bimodule mlw_map bi_ctxt m
    | _ -> assert false in
  let mlw_map, prog = foldl (fun name (mlw_map, mlw_files) ->
      if !trans_debug then begin
        Printf.fprintf stderr "Compiling %s\n" (string_of_ident name);
      end;
      let frag = IdentM.find name mlw_map in
      let mlw_map = loop name frag mlw_map in
      let mlw_file = get_mlw_file mlw_map name in
      (mlw_map, mlw_file :: mlw_files)
    ) (ini_mlw_map, []) deps in
  rev prog

(* astutil.ml -- functions on syntax trees and other utilities *)

open Ast

module Ident : Map.OrderedType with type t = ident =
struct
  type t = ident
  let compare = compare
end

module IdentM = Map.Make (Ident)
module IdentS = Set.Make (Ident)

let mk_node (loc: loc) (elt: 'a) : 'a node = {elt; loc}

let get_elts (ls: 'a node list) : 'a list =
  List.map (fun {elt;_} -> elt) ls

let string_of_ident = function
  | Id id -> id
  | Qualid (id, ids) -> String.concat "::" (id :: ids)

let rec string_of_ty ty =
  match ty.elt with
  | Tctor (name, tys) ->
    let others = List.map string_of_ty tys in
    String.concat " " (others @ [string_of_ident name])

let string_of_modifier = function
  | Public -> "public"
  | Ghost -> "ghost"
  | Modscope -> "modscope"

let string_of_loc (loc: loc) =
  Printf.sprintf "%s:%d:%d" loc.pos_fname
    loc.pos_lnum (loc.pos_cnum - loc.pos_bol + 1)

let is_left_value (v: value_in_state node) =
  match v.elt with
  | Left _ -> true
  | _ -> false

let is_right_value (v: value_in_state node) =
  match v.elt with
  | Right _ -> true
  | _ -> false

let get_program_elt_name (p: program_elt) : ident =
  match p with
  | Unr_intr i -> i.elt.intr_name
  | Unr_mdl  m -> m.elt.mdl_name
  | Rel_mdl bm -> bm.elt.bimdl_name

let interface_methods (idef: interface_def node) : meth_decl node list =
  List.filter_map (function
      | Intr_mdecl m -> Some m
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_classes (idef: interface_def node) : class_decl node list =
  List.filter_map (function
      | Intr_cdecl c -> Some c
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_datagroups (idef: interface_def node) : ident list =
  Lib.concat_filter_map (function
      | Intr_datagroup id -> Some id
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let module_methods (mdef: module_def node) : meth_def node list =
  List.filter_map (function
      | Mdl_mdef m -> Some m
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_classes (mdef: module_def node) : class_def node list =
  List.filter_map (function
      | Mdl_cdef c -> Some c
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_datagroup_names (mdef: module_def node) : ident list =
  List.filter_map (function
      | Mdl_datagroup (id, _) -> Some id
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts


(* -------------------------------------------------------------------------- *)
(* Equality modulo location info                                              *)
(* -------------------------------------------------------------------------- *)

let rec equal_ty (t: ty node) (t': ty node) =
  let open List in
  match t.elt, t'.elt with
  | Tctor (k, tys), Tctor (k', tys') ->
    k = k'
    && length tys = length tys'
    && for_all2 equal_ty tys tys'

let rec equal_exp (e: exp node) (e': exp node) =
  let open List in
  match e.elt, e'.elt with
  | Econst {elt=c; _}, Econst {elt=c'; _} -> c = c'
  | Evar id, Evar id' -> id = id'
  | Ebinop (op, e1, e2), Ebinop (op', e1', e2') ->
    op = op' && equal_exp e1 e1' && equal_exp e2 e2'
  | Eunrop (op, e), Eunrop (op', e') ->
    op = op' && equal_exp e e'
  | Esingleton e, Esingleton e' -> equal_exp e e'
  | Eimage (g, f), Eimage (g', f') -> equal_exp g g' && f = f'
  | Ecall (fn, args), Ecall (fn', args') ->
    fn = fn'
    && length args = length args'
    && for_all2 equal_exp args args'
  | _, _ -> false

let equal_let_bound_value (lb: let_bound_value node) lb' =
  match lb.elt, lb'.elt with
  | Lloc (y, f), Lloc (y', f') -> y = y' && f = f'
  | Larr (a, idx), Larr (a', idx') -> a = a' && equal_exp idx idx'
  | Lexp e, Lexp e' -> equal_exp e e'
  | _, _ -> false

let equal_let_bind (lb: let_bind) (lb': let_bind) =
  equal_let_bound_value lb.value lb'.value && lb.is_old = lb'.is_old

let equal_quantifier_bindings (qbs: quantifier_bindings) qbs' =
  let rec walk qbs qbs' =
    match qbs, qbs' with
    | [], [] -> true
    | (id, ty, eopt) :: qbs, (id', ty', eopt') :: qbs' ->
      id = id' && equal_ty ty ty'
      && begin match eopt, eopt with
        | Some e, Some e' -> equal_exp e e'
        | None, None -> true
        | _, _ -> false
      end
      && walk qbs qbs'
    | _, _ -> false in
  List.length qbs = List.length qbs' && walk qbs qbs'

let rec equal_formula (f: formula node) (f': formula node) =
  match f.elt, f'.elt with
  | Ftrue, Ftrue | Ffalse, Ffalse -> true
  | Fexp e, Fexp e' -> equal_exp e e'
  | Fnot f, Fnot f' -> equal_formula f f'
  | Fpointsto (y, f, e), Fpointsto (y', f', e') ->
    y = y' && f = f' && equal_exp e e'
  | Farray_pointsto (a, idx, e), Farray_pointsto (a', idx', e') ->
    a = a' && equal_exp idx idx' && equal_exp e e'
  | Fsubseteq (g1, g2), Fsubseteq (g1', g2') ->
    equal_exp g1 g1' && equal_exp g2 g2'
  | Fmember (x, g), Fmember (x', g') ->
    equal_exp x x' && equal_exp g g'
  | Flet (x, tyopt, value, frm), Flet (x', tyopt', value', frm') ->
    x = x' && equal_let_bind value value'
    && begin match tyopt, tyopt' with
      | Some ty, Some ty' -> equal_ty ty ty'
      | None, None -> true
      | _, _ -> false
    end
    && equal_formula frm frm'
  | Fconn (c, f1, f2), Fconn (c', f1', f2') ->
    c = c' && equal_formula f1 f1' && equal_formula f2 f2'
  | Fquant (q, qbs, frm), Fquant (q', qbs', frm') ->
    q = q' && equal_quantifier_bindings qbs qbs' && equal_formula frm frm'
  | Fold (e, value), Fold (e', value') ->
    equal_exp e e' && equal_let_bound_value value value'
  | Ftype (e, ty), Ftype (e', ty') ->
    equal_exp e e' && ty = ty'
  | _, _ -> false

let equal_atomic_command (ac: atomic_command node) ac' =
  match ac.elt, ac'.elt with
  | Skip, Skip -> true
  | Assign (x, e), Assign (x', e') -> x = x' && equal_exp e e'
  | New_class (x, k), New_class (x', k') -> x = x' && k = k'
  | New_array (x, ty, sz), New_array (x', ty', sz') ->
    x = x' && ty = ty' && equal_exp sz sz'
  | Field_deref (y, x, f), Field_deref (y', x', f') ->
    y = y' && x = x' && f = f'
  | Field_update (x, f, e), Field_update (x', f', e') ->
    x = x' && f = f' && equal_exp e e'
  | Array_access (x, a, i), Array_access (x', a', i') ->
    x = x' && a = a' && equal_exp i i'
  | Array_update (a, i, e), Array_update (a', i', e') ->
    a = a' && equal_exp i i' && equal_exp e e'
  | Call (xopt, m, args), Call (xopt', m', args') ->
    xopt = xopt' && m = m'
    && List.length args = List.length args'
    && List.for_all2 equal_exp args args'
  | _, _ -> false

let rec equal_command (c: command node) (c': command node) =
  match c.elt, c'.elt with
  | Acommand ac, Acommand ac' -> equal_atomic_command ac ac'
  | Vardecl (id, mopt, ty, c), Vardecl (id', mopt', ty', c') ->
    id = id' && mopt = mopt' && equal_ty ty ty' && equal_command c c'
  | Seq (c1, c2), Seq (c1', c2') ->
    equal_command c1 c1' && equal_command c2 c2'
  | If (e, c1, c2), If (e', c1', c2') ->
    equal_exp e e' && equal_command c1 c1' && equal_command c2 c2'
  | While (e, inv, c), While (e', inv', c') ->
    equal_exp e e' && equal_formula inv inv' && equal_command c c'
  | Assume f, Assume f' | Assert f, Assert f' ->
    equal_formula f f'
  | _, _ -> false

let equal_param_info (p: meth_param_info) (p': meth_param_info) =
  equal_ty p.param_ty p'.param_ty
  && p.param_name = p'.param_name
  && p.param_modifier = p'.param_modifier
  && p.is_non_null = p'.is_non_null

let equal_field (f: field_decl node) (f': field_decl node) : bool =
  f.elt.field_name = f'.elt.field_name
  && equal_ty f.elt.field_ty f'.elt.field_ty
  && f.elt.attribute = f'.elt.attribute

(* -------------------------------------------------------------------------- *)
(* Qualify names                                                              *)
(* -------------------------------------------------------------------------- *)

let qualify_ident (id: ident) (qual: string option) : ident =
  match qual, id with
  | None, _ -> id
  | Some qual, Id name -> Qualid (qual, [name])
  | Some qual, Qualid (prefix, name) -> Qualid (qual, prefix :: name)

let rec qualify_ty (ty: ty node) (qual: string) : ty node =
  match ty.elt with
  | Tctor(Id "int", []) | Tctor(Id "bool", [])
  | Tctor(Id "rgn", []) | Tctor(Id "unit", []) -> ty
  | Tctor(Id "array", [base_ty]) ->
    {elt = Tctor(Id "array", [qualify_ty base_ty qual]); loc = ty.loc}
  | Tctor(tyname, ts) ->
    let tyname = qualify_ident tyname (Some qual) in
    let ts = List.map (fun t -> qualify_ty t qual) ts in
    {elt = Tctor(tyname, ts); loc = ty.loc}


(* -------------------------------------------------------------------------- *)
(* Simplification                                                             *)
(* -------------------------------------------------------------------------- *)

(* FIXME: not correct *)
let rec simplify_formula (f: formula node) : formula node =
  let ret e = mk_node f.loc e in
  let is_true f =
    match f.elt with
    | Fexp ({elt = Econst {elt = Ebool true; _}; _})
    | Ftrue -> true
    | _ -> false in
  match f.elt with
  | Ftrue | Ffalse | Fold _ | Ftype _ -> f
  | Fexp e ->
    begin match e.elt with
      | Ebinop (Equal, e1, e2) when equal_exp e1 e2 -> ret Ftrue
      | Econst ({elt = Ebool true; _}) -> ret Ftrue
      | Econst ({elt = Ebool false; _}) -> ret Ffalse
      | _ -> f
    end
  | Fnot f -> ret @@ Fnot (simplify_formula f)
  | Fpointsto (x, g, e) -> ret @@ Fpointsto (x, g, e)
  | Farray_pointsto (a, i, e) -> ret @@ Farray_pointsto (a, i, e)
  | Fsubseteq (e1, e2) when equal_exp e1 e2 -> ret Ftrue
  | Fsubseteq (e1, e2) -> f
  | Fmember (i, e) -> ret @@ Fmember (i, e)
  | Flet (id, ty, value, frm) ->
    let frm = simplify_formula frm in
    ret @@ Flet (id, ty, value, frm)
  | Fconn (Conj, f1, f2) ->
    if is_true f1 then simplify_formula f2
    else if is_true f2 then simplify_formula f1
    else ret @@ Fconn (Conj, simplify_formula f1, simplify_formula f2)
  | Fconn (c, f1, f2) ->
    ret @@ Fconn (c, simplify_formula f1, simplify_formula f2)
  | Fquant (q, binds, frm) -> ret @@ Fquant (q, binds, simplify_formula frm)


(* -------------------------------------------------------------------------- *)
(* Projections                                                                *)
(* -------------------------------------------------------------------------- *)

let rec rformula_projl (r: rformula node) : formula node =
  match r.elt with
  | Rprimitive _ | Rright _ -> mk_node r.loc Ftrue
  | Rleft f | Rboth f -> f
  | Rnot rf -> mk_node r.loc @@ Fnot (rformula_projl rf)
  | Rbiequal (e, _) ->
    let equal_exp = Ebinop (Equal, e, e) in
    mk_node r.loc @@ Fexp (mk_node e.loc @@ equal_exp)
  | Ragree (g, f) ->
    let image_exp = mk_node g.loc @@ Eimage (g, f) in
    let equal_exp = Ebinop (Equal, image_exp, image_exp) in
    mk_node r.loc @@ Fexp (mk_node g.loc @@ equal_exp)
  | Rconn (c, rf1, rf2) ->
    let f1 = rformula_projl rf1 in
    let f2 = rformula_projl rf2 in
    mk_node r.loc @@ Fconn (c, f1, f2)
  | Rquant (q, (bindings, _), rf) ->
    let frm = rformula_projl rf in
    mk_node r.loc @@ Fquant (q, bindings, frm)
  | Rlet ((x, xty, xval), _, rf) ->
    let frm = rformula_projl rf in
    let let_bind = { value = xval.elt.value; is_old = xval.elt.is_old } in
    mk_node r.loc @@ Flet (x, xty, let_bind, frm)

let rec rformula_projr (r: rformula node) : formula node =
  match r.elt with
  | Rprimitive _ | Rleft _ -> mk_node r.loc Ftrue
  | Rright f | Rboth f -> f
  | Rnot rf -> mk_node r.loc @@ Fnot (rformula_projr rf)
  | Rbiequal (_, e) ->
    let equal_exp = Ebinop (Equal, e, e) in
    mk_node r.loc @@ Fexp (mk_node e.loc @@ equal_exp)
  | Ragree (g, f) ->
    let image_exp = mk_node g.loc @@ Eimage (g, f) in
    let equal_exp = Ebinop (Equal, image_exp, image_exp) in
    mk_node r.loc @@ Fexp (mk_node g.loc @@ equal_exp)
  | Rconn (c, rf1, rf2) ->
    let f1 = rformula_projr rf1 in
    let f2 = rformula_projr rf2 in
    mk_node r.loc @@ Fconn (c, f1, f2)
  | Rquant (q, (_, bindings), rf) ->
    let frm = rformula_projr rf in
    mk_node r.loc @@ Fquant (q, bindings, frm)
  | Rlet (_, (y, yty, yval), rf) ->
    let frm = rformula_projr rf in
    let let_bind = { value = yval.elt.value; is_old = yval.elt.is_old } in
    mk_node r.loc @@ Flet (y, yty, let_bind, frm)

let rec bicommand_projl (cc: bicommand node) : command node =
  match cc.elt with
  | Bisplit (c, _) -> c
  | Bisync ac -> mk_node cc.loc @@ Acommand ac
  | Biseq (bc1, bc2) ->
    let c1 = bicommand_projl bc1 in
    let c2 = bicommand_projl bc2 in
    mk_node cc.loc @@ Seq (c1, c2)
  | Bivardecl ((id, modif, ty), _, bc) ->
    let c = bicommand_projl bc in
    mk_node cc.loc @@ Vardecl (id, modif, ty, c)
  | Biif (e, _, bc1, bc2) ->
    let c1 = bicommand_projl bc1 in
    let c2 = bicommand_projl bc2 in
    mk_node cc.loc @@ If (e, c1, c2)
  | Biwhile (e, _, _, rinv, bc) ->
    let inv = rformula_projl rinv in
    let c = bicommand_projl bc in
    mk_node cc.loc @@ While (e, inv, c)
  | Biassume rf ->
    let f = rformula_projl rf in
    mk_node cc.loc @@ Assume f
  | Biassert rf ->
    let f = rformula_projl rf in
    mk_node cc.loc @@ Assert f
  | Biupdate _ ->
    let skip_node = mk_node cc.loc Skip in
    mk_node cc.loc @@ Acommand skip_node

let rec bicommand_projr (cc: bicommand node) : command node =
  match cc.elt with
  | Bisplit (_, c) -> c
  | Bisync ac -> mk_node cc.loc @@ Acommand ac
  | Biseq (bc1, bc2) ->
    let c1 = bicommand_projr bc1 in
    let c2 = bicommand_projr bc2 in
    mk_node cc.loc @@ Seq (c1, c2)
  | Bivardecl (_, (id, modif, ty), bc) ->
    let c = bicommand_projr bc in
    mk_node cc.loc @@ Vardecl (id, modif, ty, c)
  | Biif (_, e, bc1, bc2) ->
    let c1 = bicommand_projr bc1 in
    let c2 = bicommand_projr bc2 in
    mk_node cc.loc @@ If (e, c1, c2)
  | Biwhile (_, e, _, rinv, bc) ->
    let inv = rformula_projr rinv in
    let c = bicommand_projr bc in
    mk_node cc.loc @@ While (e, inv, c)
  | Biassume rf ->
    let f = rformula_projr rf in
    mk_node cc.loc @@ Assume f
  | Biassert rf ->
    let f = rformula_projr rf in
    mk_node cc.loc @@ Assert f
  | Biupdate _ ->
    let skip_node = mk_node cc.loc Skip in
    mk_node cc.loc @@ Acommand skip_node


(** annot.ml -- annotated syntax tree *)

open Lib

type ident = Ast.ident

(* Defined to aid with type checking.

   For any K, Tanyclass is considered equivalent to Tclass K.  The
   type of null (by itself) is Tanyclass.  Predicates have type Tfunc
   {params; ret} where ret = Tprop.  Axioms and lemmas have type
   Tprop.  Finally, methods have type Tmeth {params; ret}.

   The translation from Ast.ty to ity depends on a typing
   environment G = (C, M) where C is the class table and M is a set of
   extern types (math types).
*)
type ity =
  | Tint
  | Tbool
  | Trgn
  | Tunit
  | Tprop
  | Tdatagroup
  | Tanyclass
  | Tclass of ident
  | Tmath of ident * ity option
  | Tmeth of { params: ity list; ret: ity }
  | Tfunc of { params: ity list; ret: ity }

let rec equiv_ity t t' =
  let open List in
  match t, t' with
  | Tclass _, Tanyclass
  | Tanyclass, Tclass _ -> true
  | Tmath (m, t), Tmath (m',t') -> m = m' && equiv_ity_opt t t'
  | Tmeth m, Tmeth m' ->
    length m.params = length m'.params
    && for_all2 equiv_ity m.params m'.params
    && equiv_ity m.ret m.ret
  | Tfunc f, Tfunc f' ->
    length f.params = length f'.params
    && for_all2 equiv_ity f.params f'.params
    && equiv_ity f.ret f'.ret
  | _ -> t = t'

and equiv_ity_opt t t' =
  match t, t' with
  | Some t, Some t' -> equiv_ity t t'
  | _, _ -> t = t'

let rec equiv_ity_pairs tys =
  List.fold_right (fun (s,t) b -> equiv_ity s t && b) tys true

let rec string_of_ity ity =
  match ity with
  | Tint -> "int"
  | Trgn -> "rgn"
  | Tbool -> "bool"
  | Tunit -> "unit"
  | Tprop -> "<prop>"
  | Tmath (name, Some ty) ->
    "%(" ^ string_of_ity ty ^ " " ^ Astutil.string_of_ident name ^ ")"
  | Tmath (name, None) -> "%(" ^ Astutil.string_of_ident name ^ ")"
  | Tclass name -> Astutil.string_of_ident name
  | Tanyclass -> "<class>"
  | Tdatagroup -> "<datagroup>"
  | Tmeth _ -> "<method>"
  | Tfunc _ -> "<function>"

let rec qualify_ity ity qual =
  let open Astutil in
  match ity with
  | Tint | Trgn | Tbool | Tunit | Tprop | Tanyclass | Tdatagroup -> ity
  | Tclass name -> Tclass (qualify_ident name (Some qual))
  | Tmath (name, Some ty) ->
    Tmath (qualify_ident name (Some qual), Some (qualify_ity ty qual))
  | Tmath (name, None) -> Tmath (qualify_ident name (Some qual), None)
  | Tmeth m ->
    Tmeth { params = map (flip qualify_ity qual) m.params;
            ret = qualify_ity m.ret qual }
  | Tfunc f ->
    Tfunc { params = map (flip qualify_ity qual) f.params;
            ret = qualify_ity f.ret qual }

(* 'a t is the type of an annotated 'a *)
type 'a t = { ty: ity; node: 'a }

let annot ty node = { node; ty }

let ( -: ) node ty = { node; ty }

type binop = Ast.binop and unrop = Ast.unrop

type exp =
  | Econst of const_exp t
  | Evar of ident t
  | Ebinop of Ast.binop * exp t * exp t
  | Eunrop of Ast.unrop * exp t
  | Esingleton of exp t
  | Eimage of exp t * ident t
  | Ecall of ident t * exp t list

and const_exp =
  | Enull | Eunit | Eint of int | Ebool of bool | Eemptyset

type let_bound_value =
  | Lloc of ident t * ident t
  | Larr of ident t * exp t
  | Lexp of exp t

type let_bind = {
  value: let_bound_value t;
  is_old: bool;
  is_init: bool;
}

type connective = Ast.connective and quantifier = Ast.quantifier
type classname = ident

(* NOTE: formulas by themselves need not be annotated with a type.
   This is because the only annotation one may use is Prop (this
   type of annotation is not expressible in our source language).

   However, identifiers and expressions inside formulas need to be
   annotated.
*)
type formula =
  | Ftrue
  | Ffalse
  | Fexp of exp t
  | Finit of let_bound_value t
  | Fnot of formula
  | Fpointsto of ident t * ident t * exp t
  | Farray_pointsto of ident t * exp t * exp t
  | Fsubseteq of exp t * exp t
  | Fdisjoint of exp t * exp t
  | Fmember of exp t * exp t
  | Flet of ident t * let_bind t * formula
  | Fconn of connective * formula * formula
  | Fquant of quantifier * qbinders * formula
  | Fold of exp t * let_bound_value t
  | Ftype of exp t * classname list

and qbinders = (ident t * exp t option) list

type effect_kind = Ast.effect_kind

type effect_desc =
  | Effvar of ident t
  | Effimg of exp t * ident t

type effect_elt = {
  effect_kind: effect_kind;
  effect_desc: effect_desc t;
}

type effect = effect_elt list

type boundary_decl = effect_desc t list

type atomic_command =
  | Skip                                          (* skip *)
  | Assign of ident t * exp t                     (* x := E *)
  | New_class of ident t * classname              (* x := new K *)
  | New_array of ident t * classname * exp t      (* x := new T[E] *)
  | Field_deref of ident t * ident t * ident t    (* y := x.f *)
  | Field_update of ident t * ident t * exp t     (* x.f := E *)
  | Array_access of ident t * ident t * exp t     (* x := a[E] *)
  | Array_update of ident t * exp t * exp t       (* a[E] := E *)
  | Call of ident t option * ident t * ident t list (* x := m( E* ) *)

type modifier = Ast.modifier

type command =
  | Acommand of atomic_command
  | Vardecl of ident t * modifier option * ity * command
  | Seq of command * command
  | If of exp t * command * command
  | While of exp t * while_spec * command
  | Assume of formula
  | Assert of formula

and while_spec = {
  winvariants: formula list;
  wframe: effect;
}

type spec_elt =
  | Precond of formula
  | Postcond of formula
  | Effects of effect

type spec = spec_elt list

type field_decl = {
  field_name: ident t;
  field_ty: ity;
  attribute: modifier;
}

type class_decl = {
  class_name: classname;
  fields: field_decl list;
}

type class_def = Class of class_decl

type meth_decl = {
  meth_name: ident t;
  params: meth_param_info list;
  result_ty: ity;
  result_ty_is_non_null: bool;
  meth_spec: spec;
}

and meth_param_info = {
  param_name: ident t;
  param_modifier: modifier option;
  param_ty: ity;
  is_non_null: bool;
}

type meth_def = Method of meth_decl * command option

type named_formula = {
  kind: [`Axiom | `Lemma | `Predicate];
  annotation: Ast.fannot option;
  formula_name: ident t;
  params: ident t list;
  body: formula;
}

type import_directive = Ast.import_directive
and  import_kind = Ast.import_kind

type extern_decl =
  | Extern_type of ident * ident
  | Extern_const of ident * ity
  | Extern_axiom of ident
  | Extern_lemma of ident
  | Extern_predicate of { name: ident; params: ity list }
  | Extern_function of { name: ident; params: ity list; ret: ity }

type interface_elt =
  | Intr_cdecl of class_decl
  | Intr_mdecl of meth_decl
  | Intr_vdecl of modifier * ident t * ity
  | Intr_boundary of boundary_decl
  | Intr_datagroup of ident list
  | Intr_formula of named_formula
  | Intr_import of import_directive
  | Intr_extern of extern_decl

type interface_def = {
  intr_name: ident;
  intr_elts: interface_elt list;
}

type module_elt =
  | Mdl_cdef of class_def
  | Mdl_mdef of meth_def
  | Mdl_vdecl of modifier * ident t * ity
  | Mdl_datagroup of ident * ident t list
  | Mdl_formula of named_formula
  | Mdl_import of import_directive
  | Mdl_extern of extern_decl

type module_def = {
  mdl_name: ident;
  mdl_interface: ident;
  mdl_elts: module_elt list;
}

type rformula =
  | Rprimitive of {name: ident; left_args: exp t list; right_args: exp t list}
  | Rbiequal of exp t * exp t
  | Ragree of exp t * ident t
  | Rboth of formula
  | Rleft of formula
  | Rright of formula
  | Rnot of rformula
  | Rconn of connective * rformula * rformula
  | Rquant of quantifier * rqbinders * rformula
  | Rlet of rlet_binder * rlet_binder * rformula

and rlet_binder = ident t * ity * let_bind t

and rqbinders = qbinders * qbinders

type bicommand =
  | Bisplit of command * command
  | Bisync of atomic_command
  | Bivardecl of varbind * varbind * bicommand
  | Biseq of bicommand * bicommand
  | Biif of exp t * exp t * bicommand * bicommand
  | Biwhile of exp t * exp t * alignment_guard * biwhile_spec * bicommand
  | Biassume of rformula
  | Biassert of rformula
  | Biupdate of ident t * ident t (* Update the refperm *)

and alignment_guard = rformula * rformula

and varbind = ident t * modifier option * ity

and biwhile_spec = {
  biwinvariants: rformula list;
  biwframe: effect * effect;
}

type named_rformula = {
  kind: [`Axiom | `Lemma | `Predicate];
  biformula_name: ident;
  biparams: (ident t * ity) list * (ident t * ity) list;
  body: rformula;
  is_coupling: bool;
}

type bispec_elt =
  | Biprecond of rformula
  | Bipostcond of rformula
  | Bieffects of effect * effect

type bispec = bispec_elt list

type bimeth_decl = {
  bimeth_name: ident;
  bimeth_left_params: meth_param_info list;
  bimeth_right_params: meth_param_info list;
  result_ty: ity * ity;
  result_ty_is_non_null: bool * bool;
  bimeth_spec: bispec;
}

type bimeth_def = Bimethod of bimeth_decl * bicommand option

type bimodule_elt =
  | Bimdl_formula of named_rformula
  | Bimdl_mdef of bimeth_def
  | Bimdl_extern of extern_decl
  | Bimdl_import of import_directive

type bimodule_def = {
  bimdl_name: ident;
  bimdl_left_impl: ident;
  bimdl_right_impl: ident;
  bimdl_elts: bimodule_elt list;
}

type program_elt =
  | Unary_interface of interface_def
  | Unary_module of module_def
  | Relation_module of bimodule_def

type penv = program_elt Astutil.IdentM.t


(* -------------------------------------------------------------------------- *)
(* Utility functions on effects                                               *)
(* -------------------------------------------------------------------------- *)

let dest_eff e = (e.effect_kind, e.effect_desc)

let is_read e = e.effect_kind = Read
let is_write e = e.effect_kind = Write

let mk_eff_var k x =
  {effect_kind = k; effect_desc = Effvar x -: x.ty}

let mk_eff_img k g f =
  {effect_kind = k; effect_desc = Effimg (g,f) -: Trgn}

let rdvar x = mk_eff_var Read x
let wrvar x = mk_eff_var Write x

let rdimg g f = mk_eff_img Read g f
let wrimg g f = mk_eff_img Write g f

let is_eff_img (e: effect_desc t) =
  match e.node with
  | Effimg (_, _) -> true
  | _ -> false

let is_eff_var (e: effect_desc t) = not (is_eff_img e)

let is_rdvar e = is_eff_var e.effect_desc && is_read e
let is_rdimg e = is_eff_img e.effect_desc && is_read e
let is_wrvar e = is_eff_var e.effect_desc && is_write e
let is_wrimg e = is_eff_var e.effect_desc && is_write e

let sngl x = Esingleton (Evar x -: x.ty) -: Trgn

let rds, wrs =
  let kind e = e.effect_kind in
  filter ((=) Ast.Read % kind), filter ((=) Ast.Write % kind)

let r2w = map (fun e -> {e with effect_kind = Write}) % rds

let w2r = map (fun e -> {e with effect_kind = Read}) % wrs

(* Convert a boundary_decl to an effect *)
let eff_of_bnd (b: boundary_decl) : effect =
  map (fun e -> {effect_kind = Read; effect_desc = e}) b

(* Convert a list of (read) effects to a boundary  *)
let bnd_of_eff (eff: effect) : boundary_decl =
  let cons e es = match dest_eff e with
    | (Read, e') -> e' :: es
    | (Write, _) -> invalid_arg "bnd_of_eff" in
  foldr cons [] eff


(* -------------------------------------------------------------------------- *)
(* Footprints of expressions and formulas                                     *)
(* -------------------------------------------------------------------------- *)

(* Footprint of an expression *)
let ftpt_exp (e: exp t) : effect =
  let rec aux eff e = match e.node with
    | Econst _ -> eff
    | Evar x -> rdvar x :: eff
    | Ebinop (_, e1, e2) -> aux (aux eff e1) e2
    | Eunrop (_, e) -> aux eff e
    | Esingleton e -> aux eff e
    | Eimage (g, f) -> aux (rdimg g f :: eff) g
    | Ecall (m, es) -> List.fold_left aux eff es in
  aux [] e

(* Footprint of a let_bound_value *)
let ftpt_lb (lb: let_bound_value t) : effect =
  match lb.node with
  | Lloc (x, f) -> [rdvar x; rdimg (sngl x) f]
  | Larr (a, i) -> [rdvar a]
  | Lexp e -> ftpt_exp e

(* Footprint of a formula *)
(* FIXME: Review ftpt(a[i]=e)--should probably read the slots field as well, but
   we need the class table to figure out the name of the slots field. *)
let ftpt_formula (f: formula) : effect =
  let rec aux eff = function
    | Ftrue | Ffalse -> eff
    | Fexp e -> ftpt_exp e @ eff
    | Finit lb -> ftpt_lb lb @ eff
    | Fnot f -> aux eff f
    | Fpointsto (x, f, e) -> rdvar x :: rdimg (sngl x) f :: ftpt_exp e @ eff
    | Farray_pointsto (a, i, e) -> rdvar a :: ftpt_exp e @ eff
    | Fmember (e1, e2) -> ftpt_exp e1 @ ftpt_exp e2 @ eff
    | Fsubseteq (e1, e2) -> ftpt_exp e1 @ ftpt_exp e2 @ eff
    | Fdisjoint (e1, e2) -> ftpt_exp e1 @ ftpt_exp e2 @ eff
    | Flet (x, lb, f) -> aux (rdvar x :: ftpt_lb lb.node.value @ eff) f
    | Fconn (_, f1, f2) -> aux (aux eff f1) f2
    | Fquant _ -> invalid_arg "ftpt_formula: expected an atomic formula"
    | Fold (e, lb) -> ftpt_exp e @ ftpt_lb lb @ eff
    | Ftype (e, _) -> ftpt_exp e @ eff in
  aux [] f


(* -------------------------------------------------------------------------- *)
(* Functions that deal with free variables                                    *)
(* -------------------------------------------------------------------------- *)

(* Set of identifiers *)
module IdS = Astutil.IdentS

let free_vars_exp e =
  let rec aux fv e = match e.node with
    | Econst _ -> fv
    | Evar x -> IdS.add x.node fv
    | Ebinop (_, e1, e2) -> aux (aux fv e1) e2
    | Eunrop (_, e) -> aux fv e
    | Esingleton e -> aux fv e
    | Eimage (g, f) -> aux (IdS.add f.node fv) g
    | Ecall (id, es) -> List.fold_left aux (IdS.add id.node fv) es in
  aux IdS.empty e

let free_vars_let_bound_value = function
  | Lloc (x, f) -> IdS.of_list [x.node; f.node]
  | Larr (a, i) -> IdS.add a.node (free_vars_exp i)
  | Lexp e -> free_vars_exp e

let rec free_vars_formula f = match f with
  | Ftrue | Ffalse -> IdS.empty
  | Finit e -> free_vars_let_bound_value e.node
  | Fexp e -> free_vars_exp e
  | Fnot f -> free_vars_formula f
  | Fpointsto (x, f, e) ->
    let s = IdS.of_list [x.node; f.node] in
    IdS.union s (free_vars_exp e)
  | Farray_pointsto (a, i, e) ->
    IdS.add a.node (IdS.union (free_vars_exp i) (free_vars_exp e))
  | Fsubseteq (e1, e2) | Fdisjoint (e1, e2)
  | Fmember (e1, e2) -> IdS.union (free_vars_exp e1) (free_vars_exp e2)
  | Flet (x, {node={value=lb; _}; _}, f) ->
    let lb_fv = free_vars_let_bound_value lb.node in
    let f_fv  = free_vars_formula f in
    IdS.union lb_fv (IdS.diff f_fv (IdS.singleton x.node))
  | Fconn (_, f1, f2) -> IdS.union (free_vars_formula f1) (free_vars_formula f2)
  | Fquant (q, qbinds, f) ->
    let f_fv = free_vars_formula f in
    let bind_names = List.map (fun (x,_) -> x.node) qbinds in
    let es_fv =
      List.map (function
          | (_, None) -> IdS.empty
          | (_, Some e) -> free_vars_exp e
        ) qbinds in
    let es_fv = List.fold_left IdS.union IdS.empty es_fv in
    IdS.union es_fv (IdS.diff f_fv (IdS.of_list bind_names))
  | Fold (e, {node=lb; _}) ->
    IdS.union (free_vars_exp e) (free_vars_let_bound_value lb)
  | Ftype (e, k) -> free_vars_exp e

let rec free_vars_rformula = function
  | Rprimitive {name=m; left_args; right_args} ->
    let args = left_args @ right_args in
    let args_fv = List.map free_vars_exp args in
    IdS.add m (List.fold_left IdS.union IdS.empty args_fv)
  | Rbiequal (e, e') -> IdS.union (free_vars_exp e) (free_vars_exp e')
  | Ragree (e, f) -> IdS.add f.node (free_vars_exp e)
  | Rboth f | Rleft f | Rright f -> free_vars_formula f
  | Rnot rf -> free_vars_rformula rf
  | Rconn (_, rf1, rf2) ->
    IdS.union (free_vars_rformula rf1) (free_vars_rformula rf2)
  | Rquant (q, (lbinds, rbinds), rf) ->
    let rf_fv = free_vars_rformula rf in
    let names = List.map (fun (x,_) -> x.node) (lbinds @ rbinds) in
    let exps  =
      List.map (function
          | (_, None) -> IdS.empty
          | (_, Some e) -> free_vars_exp e
        ) (lbinds @ rbinds) in
    let exp_fvs = List.fold_left IdS.union IdS.empty exps in
    IdS.union exp_fvs (IdS.diff rf_fv (IdS.of_list names))
  | Rlet ((lid, _, {node={value=llb; _};_}),
          (rid, _, {node={value=rlb; _};_}), rf) ->
    let rf_fv = free_vars_rformula rf in
    let rf_fv = IdS.diff rf_fv (IdS.of_list [lid.node; rid.node]) in
    let llb_fv = free_vars_let_bound_value llb.node in
    let rlb_fv = free_vars_let_bound_value rlb.node in
    IdS.union llb_fv (IdS.union rlb_fv rf_fv)


(* -------------------------------------------------------------------------- *)
(* Projections                                                                *)
(* -------------------------------------------------------------------------- *)

let rec projl_rformula (rf: rformula) : formula =
  match rf with
  | Rprimitive _ | Rright _ -> Ftrue
  | Rleft f | Rboth f -> f
  | Rnot rf -> Fnot (projl_rformula rf)
  | Rbiequal (e, _) -> Fexp (Ebinop (Equal, e, e) -: Tbool)
  | Ragree (g, f) ->
    let img_exp = Eimage (g, f) -: Trgn in
    let equal_exp = Ebinop (Equal, img_exp, img_exp) in
    Fexp (equal_exp -: Tbool)
  | Rconn (c, rf1, rf2) -> Fconn (c, projl_rformula rf1, projl_rformula rf2)
  | Rquant (q, (bindings, _), rf) -> Fquant (q, bindings, projl_rformula rf)
  | Rlet ((x, _, xval), _, rf) -> Flet (x, xval, projl_rformula rf)

let rec projr_rformula (rf: rformula) : formula =
  match rf with
  | Rprimitive _ | Rleft _ -> Ftrue
  | Rright f | Rboth f -> f
  | Rnot rf -> Fnot (projr_rformula rf)
  | Rbiequal (_, e) -> Fexp (Ebinop (Equal, e, e) -: Tbool)
  | Ragree (g, f) ->
    let img_exp = Eimage (g, f) -: Trgn in
    let equal_exp = Ebinop (Equal, img_exp, img_exp) in
    Fexp (equal_exp -: Tbool)
  | Rconn (c, rf1, rf2) -> Fconn (c, projr_rformula rf1, projr_rformula rf2)
  | Rquant (q, (_, bindings), rf) -> Fquant (q, bindings, projr_rformula rf)
  | Rlet (_, (x, _, xval), rf) -> Flet (x, xval, projr_rformula rf)

let rec projl (cc: bicommand) : command =
  match cc with
  | Bisplit (cl, _) -> cl
  | Bisync ac -> Acommand ac
  | Biseq (cc1, cc2) -> Seq (projl cc1, projl cc2)
  | Bivardecl ((id, modif, ty), _, cc) -> Vardecl (id, modif, ty, projl cc)
  | Biif (e, _, cc1, cc2) -> If (e, projl cc1, projl cc2)
  | Biwhile (e, _, _, {biwinvariants; biwframe=(eff, _)}, cc) ->
    let winvariants = map projl_rformula biwinvariants in
    While (e, {winvariants; wframe=eff}, projl cc)
  | Biassume rf -> Assume (projl_rformula rf)
  | Biassert rf -> Assert (projl_rformula rf)
  | Biupdate _ -> Acommand Skip

let rec projr (cc: bicommand) : command =
  match cc with
  | Bisplit (_, cr) -> cr
  | Bisync ac -> Acommand ac
  | Biseq (cc1, cc2) -> Seq (projr cc1, projr cc2)
  | Bivardecl (_, (id, modif, ty), cc) -> Vardecl (id, modif, ty, projr cc)
  | Biif (_, e, cc1, cc2) -> If (e, projr cc1, projr cc2)
  | Biwhile (_, e, _, {biwinvariants; biwframe=(_,eff)}, cc) ->
    let winvariants = map projr_rformula biwinvariants in
    While (e, {winvariants; wframe=eff}, projr cc)
  | Biassume rf -> Assume (projr_rformula rf)
  | Biassert rf -> Assert (projr_rformula rf)
  | Biupdate _ -> Acommand Skip


(* -------------------------------------------------------------------------- *)
(* Simplifications and rewritings                                             *)
(* -------------------------------------------------------------------------- *)

(* reassoc f = f'

   any subterm in f of the form f1 /\ f2 /\ f3 is rewritten to
   (f1 /\ f2) /\ f3 in f'.
*)
let rec reassoc (f: formula) : formula =
  match f with
  | Fconn (Conj, f1, f2) ->
    let f1' = reassoc f1 in
    let f2' = reassoc f2 in
    begin match f2' with
      | Fconn (Conj, t1, t2) -> Fconn (Conj, Fconn (Conj, f1', t1), t2)
      | _ -> Fconn (Conj, f1', f2')
    end
  | Fnot f -> Fnot (reassoc f)
  | Flet (id, v, f) -> Flet (id, v, reassoc f)
  | Fconn (c, f1, f2) -> Fconn (c, reassoc f1, reassoc f2)
  | Fquant (q, qbinds, f) -> Fquant (q, qbinds, reassoc f)
  | _ -> f

(* simplify_formula f = f'

   rewrite every occurence of true /\ H or H /\ true in f to H in f'.
*)
let rec simplify_formula (f: formula) : formula =
  match f with
  | Ftrue -> Ftrue
  (* FIXME: Using builtin equality below *)
  | Fexp {node=Ebinop (Equal, e1, e2); _} when e1 = e2 -> Ftrue
  | Fconn (Conj, f1, f2) ->
    let f1' = simplify_formula f1 in
    let f2' = simplify_formula f2 in
    begin match f1', f2' with
      | Ftrue, h
      | h, Ftrue
      | Fexp {node=Econst {node=Ebool true; _};_}, h
      | h, Fexp {node=Econst {node=Ebool true; _};_} -> h
      | _, _ -> Fconn (Conj, f1', f2')
    end
  | Fnot f -> Fnot (simplify_formula f)
  | Flet (id, v, f) -> Flet (id, v, simplify_formula f)
  | Fconn (c, f1, f2) -> Fconn (c, simplify_formula f1, simplify_formula f2)
  | Fquant (q, qbinds, f) -> Fquant (q, qbinds, simplify_formula f)
  | _ -> f

let projl_rformula_simplify (rf: rformula) : formula =
  let f = projl_rformula rf in
  simplify_formula (reassoc f)

let projr_rformula_simplify (rf: rformula) : formula =
  let f = projr_rformula rf in
  simplify_formula (reassoc f)


(* rw_skip c = c'

   Rewrite rules:

     skip; d --> skip; d            d; skip --> skip; d

     c; (skip; d) --> skip; (c; d)  c; (d; skip) --> skip; (c; d)

     (skip; c); d --> skip; (c; d)  (c; skip); d --> skip; (c; d)

*)
let rec rw_skip (c: command) : command =
  match c with
  | Acommand ac -> Acommand ac
  | Vardecl (id, modif, ty, c) -> Vardecl (id, modif, ty, rw_skip c)
  | Seq (c1, c2) ->
    let c1' = rw_skip c1 in
    let c2' = rw_skip c2 in
    begin match c1', c2' with
      | Acommand Skip, d | d, Acommand Skip -> Seq (Acommand Skip, d)
      | _, Seq (Acommand Skip, d) | _, Seq (d, Acommand Skip) ->
        Seq (Acommand Skip, Seq (c1', d))
      | Seq (Acommand Skip, d), _ | Seq (d, Acommand Skip), _ ->
        Seq (Acommand Skip, Seq (d, c2'))
      | _, _ -> Seq (c1', c2')
    end
  | If (e, c1, c2) -> If (e, rw_skip c1, rw_skip c2)
  | While (e, f, c) -> While (e, f, rw_skip c)
  | _ -> c


(* simplify_command c = c'

   rewrite every occurence of skip ; D or D ; skip in c to D in c';
   additionally, rewrite assert { f } and assume { f } in c to skip in c'.
*)
let rec simplify_command (c: command) : command =
  match c with
  | Acommand ac -> Acommand ac
  | Vardecl (id, modif, ty, c) -> Vardecl (id, modif, ty, simplify_command c)
  | Seq (c1, c2) ->
    let c1' = simplify_command c1 in
    let c2' = simplify_command c2 in
    begin match c1', c2' with
      | Acommand Skip, d | d, Acommand Skip -> d
      | _, _ -> Seq (c1', c2')
    end
  | If (e, c1, c2) -> If (e, simplify_command c1, simplify_command c2)
  | While (e, {winvariants; wframe}, c) ->
    let winvariants = map simplify_formula winvariants in
    While (e, {winvariants; wframe}, simplify_command c)
  | Assume _ | Assert _ -> Acommand Skip

(* rewrite ((c1 ; c2) ; c3) to (c1 ; (c2 ; c3)) *)
let rec reassoc_command (c: command) : command =
  match c with
  | Seq (c1, c2) ->
    let c1' = reassoc_command c1 in
    let c2' = reassoc_command c2 in
    begin match c1' with
      | Seq (c1, c2) -> Seq (c1, reassoc_command (Seq (c2, c2')))
      | _ -> Seq (c1', c2')
    end
  | Vardecl (id, modif, ty, c) -> Vardecl (id, modif, ty, reassoc_command c)
  | If (e, c1, c2) -> If (e, reassoc_command c1, reassoc_command c2)
  | While (e, f, c) -> While (e, f, reassoc_command c)
  | c -> c

let projl_simplify (cc: bicommand) : command =
  let c = projl cc in
  reassoc_command @@ simplify_command (rw_skip c)

let projr_simplify (cc: bicommand) : command =
  let c = projr cc in
  reassoc_command @@ simplify_command (rw_skip c)

let rw_command = reassoc_command % simplify_command % rw_skip


(* -------------------------------------------------------------------------- *)
(* Equality mod assertions/assumptions/invariants/extra locals                *)
(* -------------------------------------------------------------------------- *)

let rec eqf_command c c' = match c, c' with
  | Acommand ac, Acommand ac' -> ac = ac'
  | Vardecl (id, m, ty, c), Vardecl (id', m', ty', c') ->
    id = id' && m = m' && ty = ty' && eqf_command c c'
  | Vardecl (id, m, ty, c), c' -> eqf_command c c'
  | c, Vardecl (id, m, ty, c') -> eqf_command c c'
  | Seq (c1, c2), Seq (c1', c2') -> eqf_command c1 c1' && eqf_command c2 c2'
  | If (e, c1, c2), If (e', c1', c2') ->
    e = e' && eqf_command c1 c1' && eqf_command c2 c2'
  | While (e, _, c), While (e', _, c') -> e = e' && eqf_command c c'
  | Assume _, Assume _ -> true
  | Assert _, Assert _ -> true
  | _, _ -> false

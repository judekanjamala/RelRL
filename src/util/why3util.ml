(** why3util -- utility functions to work with Why3 *)

open Lib
open Why3


(* -------------------------------------------------------------------------- *)
(* Utility structures                                                         *)
(* -------------------------------------------------------------------------- *)

module Ordered_Ptree_qualid =
struct
  type t = Ptree.qualid

  let rec compare s t =
    let open Ptree in
    let comp = Stdlib.compare in
    match s, t with
    | Qident s, Qident t -> comp s.id_str t.id_str
    | Qident s, _ -> -1
    | _, Qident s -> 1
    | Qdot (qs, s), Qdot (qt, t) ->
      let res = compare qs qt in
      if res = 0 then comp s.id_str t.id_str else res
end

module QualidS = Set.Make (Ordered_Ptree_qualid)
module QualidM = Map.Make (Ordered_Ptree_qualid)


(* -------------------------------------------------------------------------- *)
(* Constructing parse trees                                                   *)
(* -------------------------------------------------------------------------- *)

(* Taken from Why3's API tutorials *)

let mk_ident (s: string) : Ptree.ident =
  { id_str = s;
    id_ats = [];
    id_loc = Loc.dummy_position }

let mk_qualid (l: string list) : Ptree.qualid =
  let rec aux l =
    match l with
    | [] -> assert false
    | [x] -> Ptree.Qident(mk_ident x)
    | x::r -> Ptree.Qdot(aux r, mk_ident x) in
  aux (List.rev l)

let string_list_of_qualid (q: Ptree.qualid) : string list =
  let rec aux l = function
    | Ptree.Qident x -> x.id_str :: l
    | Ptree.Qdot (ql, x) -> aux (x.id_str :: l) ql in
  aux [] q

let qualid_of_ident (id: Ptree.ident) : Ptree.qualid =
  mk_qualid [id.id_str]

let ident_of_qualid (ql: Ptree.qualid) : Ptree.ident =
  match ql with
  | Qident id -> id
  | Qdot _ -> invalid_arg "ident_of_qualid"

let mk_infix (op: string) : Ptree.ident =
  mk_ident (Ident.op_infix op)

let use_import (l: string list) : Ptree.decl =
  let qid_id_opt = (mk_qualid l, None) in
  Duseimport (Loc.dummy_position, false, [qid_id_opt])

let use_export (l: string list) : Ptree.decl =
  let qid = mk_qualid l in
  Duseexport qid

let mk_expr (e: Ptree.expr_desc) : Ptree.expr =
  { expr_desc = e;
    expr_loc = Loc.dummy_position }

let mk_term (t: Ptree.term_desc) : Ptree.term =
  { term_desc = t;
    term_loc = Loc.dummy_position }

let mk_pat (p: Ptree.pat_desc) : Ptree.pattern =
  { pat_desc = p;
    pat_loc = Loc.dummy_position }

let pat_var (id: Ptree.ident) : Ptree.pattern =
  mk_pat (Pvar id)

let mk_var (id: Ptree.ident) : Ptree.term =
  mk_term (Tident (Qident id))

let mk_qvar (id: Ptree.qualid) : Ptree.term =
  mk_term (Tident id)

let param0 = [Loc.dummy_position, None, false, Some (Ptree.PTtuple [])]
let param1 id ty = [Loc.dummy_position, Some id, false, Some ty]

let mk_const (i: int) : Constant.constant =
  Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = BigInt.of_int i})

let mk_tconst (i: int) : Ptree.term = mk_term (Tconst (mk_const i))

let mk_econst (i: int) : Ptree.expr = mk_expr (Econst (mk_const i))

let mk_tapp (f: Ptree.qualid) (l: Ptree.term list) : Ptree.term =
  mk_term (Tidapp (f, l))

let mk_eapp (f: Ptree.qualid) (l: Ptree.expr list) : Ptree.expr =
  mk_expr (Ptree.Eidapp (f, l))

let mk_evar (x: Ptree.ident) : Ptree.expr = mk_expr (Eident (Qident x))

let mk_qevar (x: Ptree.qualid) : Ptree.expr = mk_expr (Eident x)

let mk_param id gho ty : Ptree.param =
  (Loc.dummy_position, Some id, gho, ty)

let mk_binder x gho (ty: Ptree.pty option) : Ptree.binder =
  (Loc.dummy_position, Some x, gho, ty)

let mk_quant quantif binders frm : Ptree.term =
  mk_term @@ Tquant (quantif, binders, [], frm)

(* mk_implies [t1; t2; ...; tn] = ``t1 -> t2 -> ... -> tn'' *)
let mk_implies (ts: Ptree.term list) : Ptree.term =
  if is_nil ts then failwith "mk_implies: empty list"
  else foldr1 (fun h t -> mk_term (Tbinop (h, Dterm.DTimplies, t))) ts

(* mk_conjs [t1; t2; ...; tn] = ``t1 /\ t2 /\ ... /\ tn'' *)
let mk_conjs (ts: Ptree.term list) : Ptree.term =
  if is_nil ts then failwith "mk_conjs: empty list"
  else foldr1 (fun h t -> mk_term (Tbinop (h, Dterm.DTand, t))) ts

(* safe_mk_conjs ts = ts'

   if ts = [], then ts' = []
   otherwise ts' = mk_conjs ts
 *)
let safe_mk_conjs (ts: Ptree.term list) : Ptree.term list =
  match ts with
  | [] -> []
  | _ -> [mk_conjs ts]

let mk_conjs_default (ts: Ptree.term list) (t: Ptree.term) : Ptree.term =
  let conj t1 t2 = mk_term (Tbinop (t1, Dterm.DTand, t2)) in
  foldr1 conj (t::ts)

let mk_spec pre post reads writes : Ptree.spec =
  { sp_pre = pre;               (* preconditions *)
    sp_post = post;             (* postconditions *)
    sp_xpost = [];              (* exceptional postconditions *)
    sp_reads = reads;           (* reads clause *)
    sp_writes = writes;         (* writes clause *)
    sp_alias = [];              (* alias clause *)
    sp_variant = [];            (* variant for recursive functions *)
    sp_checkrw = false;         (* should reads and writes be checked? *)
    sp_diverge = false;         (* does the function diverge? *)
    sp_partial = false          (* is the function partial? *)
  }

let empty_spec : Ptree.spec = mk_spec [] [] [] []

let mk_spec_simple pre post writes : Ptree.spec =
  { sp_pre = pre;
    sp_post = post;
    sp_xpost = [];
    sp_reads = [];
    sp_writes = writes;
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false
  }

let mk_ldecl ident params lty def : Ptree.logic_decl =
  { ld_loc = Loc.dummy_position;
    ld_ident = ident;
    ld_params = params;
    ld_type = Some lty;
    ld_def = def
  }

let mk_abstract_expr params ret_ty spec : Ptree.expr =
  let mask = Ity.MaskVisible in
  mk_expr @@ Eany (params, Expr.RKnone, Some ret_ty, mk_pat Pwild, mask, spec)

let mk_ensures frm : Ptree.post =
  Loc.dummy_position, [pat_var (mk_ident "result"), frm]


(* -------------------------------------------------------------------------- *)
(* Default definitions                                                        *)
(* -------------------------------------------------------------------------- *)

let mk_pair_ty t1 t2 : Ptree.pty = PTtuple [t1; t2]

let rec mk_explain_attr msg =
  let expl = "expl:" ^ msg in
  Ptree.ATstr (Ident.create_attribute expl)

and explain_term t msg = mk_term (Tattr (mk_explain_attr msg, t))
and explain_expr t msg = mk_expr (Eattr (mk_explain_attr msg, t))

let suppress_unused_warning term =
  let unused = Ident.create_attribute "W:unused_variable:N" in
  mk_term (Tattr (Ptree.ATstr unused, term))


(* -------------------------------------------------------------------------- *)
(* Wrappers around Why3 pretty printing functions                             *)
(* -------------------------------------------------------------------------- *)

let wrap_pp pp e : unit =
  pp Format.std_formatter e;
  Format.pp_print_newline Format.std_formatter ();
  Format.pp_print_flush Format.std_formatter ()

let show_pty  = wrap_pp Mlw_printer.pp_pty
let show_expr = wrap_pp Mlw_printer.pp_expr
let show_term = wrap_pp Mlw_printer.pp_term
let show_decl = wrap_pp Mlw_printer.pp_decl
let show_mlw  = wrap_pp Mlw_printer.pp_mlw_file

(* -------------------------------------------------------------------------- *)
(* Convenient forms for building Why3 parse trees                             *)
(* -------------------------------------------------------------------------- *)

module Build_operators = struct
  (* DO NOT rely on operator precedences and associativity when using
     this module.  Parenthesize! *)

  (* right associative *)
  let ( ^==> ) t1 t2 = mk_term (Tbinop (t1, Dterm.DTimplies, t2))

  (* left associative *)
  let ( <==> ) t1 t2 = mk_term (Tbinop (t1, Dterm.DTiff, t2))

  (* left associative *)
  let ( ==. ) t1 t2 = mk_term (Tinfix (t1, mk_infix "=", t2))

  let ( =/=. ) t1 t2 = mk_term (Tinfix (t1, mk_infix "<>", t2))

  (* right associative *)
  let ( ^&& ) t1 t2 = mk_term (Tbinop (t1, Dterm.DTand, t2))

  let ( ^& ) e1 e2 = mk_expr (Eand (e1, e2))

  (* right associative *)
  let ( ^|| ) t1 t2 = mk_term (Tbinop (t1, Dterm.DTor, t2))

  let ( ^| ) e1 e2 = mk_expr (Eor (e1, e2))

  (* prefix *)
  let ( ~. ) x = mk_ident x

  (* prefix *)
  let ( ~* ) x = mk_var x

  (* prefix *)
  let ( ~% ) x = mk_term x

  (* prefix *)
  let ( ~^ ) x = mk_expr (Enot x)

  (* left associative *)
  let ( %. ) s f = Ptree.Qdot(s, f)

  let mk_term_app f args =
    List.fold_left (fun acc e -> mk_term (Tapply (acc, e))) (mk_qvar f) args

  (* left associative *)
  let ( <*> ) f args = mk_term (Tidapp(f, args))
  let ( <$> ) f args = mk_expr (Eidapp(f, args))

  let bindvar (x, ty) s = ((x, ty), s)
  let return t s = (t, s)
  let build_term (t: 's -> ('a * 's)) = fst (t [])

  (* let+! and let+? can be used to create universally and
     existentially quantified formulas.  For example, one may say

         let+! p = bindvar (mk_ident "p", int_type) in
         let+? q = bindvar (mk_ident "q", int_type) in
         return ((mk_var p) ==. (mk_var q))

     to build the Why3 term: (forall p:int. exists q:int. p = q).

     Sequences of forall's and exist's are handled so that

         let+! p = bindvar (mk_ident "p", ...) in
         let+! q = bindvar (mk_ident "q", ...) in
         ...

     generates (forall p:int, q:int. ...) instead of
     (forall p:int. forall q:int. ...).
     Such chains are appropriately broken if quantifiers are mixed.
  *)
  let ( let+! ) (m: 's->('a*'s)) (k: 'a->'s->('b*'s)) : 's->('b*'s) = fun s ->
    let (x, ty), binders = m s in
    let term, binders' = k (x, ty) binders in
    let xbind = mk_binder x false (Some ty) in
    match term.Ptree.term_desc with
    | Tquant(Dterm.DTforall, _, metas, inner) ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTforall, binds, metas, inner)) in
      term', binds
    | Tquant(Dterm.DTexists, _, _, _) ->
      let term' = mk_term (Tquant(Dterm.DTforall, [xbind], [], term)) in
      term', [xbind]
    | _ ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTforall, binds, [], term)) in
      term', binds

  let ( let+? ) (m: 's->('a*'s)) (k: 'a->'s->('b*'s)) : 's->('b*'s) = fun s ->
    let (x, ty), binders = m s in
    let (term, binders') = k (x, ty) binders in
    let xbind = mk_binder x false (Some ty) in
    match term.Ptree.term_desc with
    | Tquant (Dterm.DTexists, _, metas, inner) ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTexists, binds, metas, inner)) in
      term', binds
    | Tquant (Dterm.DTforall, _, _, _) ->
      let term' = mk_term (Tquant(Dterm.DTexists, [xbind], [], term)) in
      term', [xbind]
    | _ ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTexists, binds, [], term)) in
      term', binds
end

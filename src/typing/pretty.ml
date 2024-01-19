 (** pretty.ml -- pretty printer for annotated syntax trees *)

open Annot
open Format

let pp_ident outf id = fprintf outf "%s" @@ Astutil.string_of_ident id

let pp_idents outf ids =
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_ident outf ids

let pp_ity outf ty = fprintf outf "%s" @@ string_of_ity ty

let pp_binop outf (op: Ast.binop) =
  match op with
  | Plus   -> fprintf outf "+"
  | Minus  -> fprintf outf "-"
  | Mult   -> fprintf outf "*"
  | Div    -> fprintf outf "/"
  | Mod    -> fprintf outf "mod"
  | Equal  -> fprintf outf "="
  | Nequal -> fprintf outf "<>"
  | Leq    -> fprintf outf "<="
  | Geq    -> fprintf outf ">="
  | Gt     -> fprintf outf ">"
  | Lt     -> fprintf outf "<"
  | And    -> fprintf outf "and"
  | Or     -> fprintf outf "or"
  | Union  -> fprintf outf "union"
  | Inter  -> fprintf outf "inter"
  | Diff   -> fprintf outf "diff"

let max_precedence = 100        (* ` has max precedence *)

let binop_precedence (op: Ast.binop) =
  match op with
  | Union  -> 50
  | Inter  -> 50
  | Diff   -> 60
  | Mult   -> 40
  | Div    -> 40
  | Mod    -> 50
  | Plus   -> 30
  | Minus  -> 30
  | Equal  -> 20
  | Nequal -> 20
  | Leq    -> 10
  | Geq    -> 10
  | Gt     -> 10
  | Lt     -> 10
  | And    -> 5
  | Or     -> 3

let pp_unrop outf (op: Ast.unrop) =
  match op with
  | Uminus -> fprintf outf "-"
  | Not    -> fprintf outf "not"

let unrop_precedence (op: Ast.unrop) =
  match op with
  | Uminus -> 60
  | Not    -> 60

let rec pp_exp' k outf e =
  match e.node with
  | Econst ce -> fprintf outf "%a" pp_const_exp ce.node
  | Evar id -> fprintf outf "%a" pp_ident id.node
  | Ebinop (op, e1, e2) ->
    let prec = binop_precedence op in
    let pp' = pp_exp' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' e1 pp_binop op pp' e2
    else fprintf outf "@[%a@ %a@ %a@]" pp' e1 pp_binop op pp' e2
  | Eunrop (op, e) ->
    let prec = unrop_precedence op in
    let pp' = pp_exp' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a)@]" pp_unrop op pp' e
    else fprintf outf "@[%a@ %a@]" pp_unrop op pp' e
  | Esingleton e -> fprintf outf "@[{%a}@]" (pp_exp' k) e
  | Eimage (g, f) ->
     fprintf outf "@[%a`%a@]" (pp_exp' max_precedence) g pp_ident f.node
  | Esubrgn (g, k) ->
     fprintf outf "@[%a of %a@]" pp_ident k (pp_exp' max_precedence) g
  | Ecall (fn, args) ->
     fprintf outf "@[%a(@[%a@])@]" pp_ident fn.node pp_exps args
  | Einit e ->
     fprintf outf "@[(init %a)@]" (pp_exp' k) e


and pp_exps outf exps =
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_exp outf exps

and pp_const_exp outf ce =
  match ce with
  | Enull     -> fprintf outf "null"
  | Eunit     -> fprintf outf "()"
  | Eint i    -> fprintf outf "%d" i
  | Ebool b   -> fprintf outf "%B" b
  | Eemptyset -> fprintf outf "{}"

and pp_exp outf e = pp_exp' 0 outf e

let pp_let_bound_value outf e =
  match e with
  | Lloc (x, f) -> fprintf outf "@[%a.%a@]" pp_ident x.node pp_ident f.node
  | Larr (a, idx) -> fprintf outf "@[%a[%a]@]" pp_ident a.node pp_exp idx
  | Lexp e -> pp_exp outf e

let pp_let_bind outf e =
  let value = e.value.node in
  if e.is_old then fprintf outf "@[old(%a)@]" pp_let_bound_value value
  else pp_let_bound_value outf value

let pp_connective outf (conn: Ast.connective) =
  match conn with
  | Conj -> fprintf outf "/\\"
  | Disj -> fprintf outf "\\/"
  | Imp  -> fprintf outf "->"
  | Iff  -> fprintf outf "<->"

let connective_precedence (conn: Ast.connective) =
  match conn with
  | Conj -> 50
  | Disj -> 60
  | Imp  -> 30
  | Iff  -> 20

let pp_quantifier outf = function
  | Ast.Forall -> fprintf outf "@[forall@]"
  | Ast.Exists -> fprintf outf "@[exists@]"

let pp_ity_non_null is_non_null outf ty =
  if is_non_null then pp_ity outf ty else fprintf outf "@[%a?@]" pp_ity ty

let pp_qbinders outf qbinds =
  let pp_qbind out {name; in_rgn; is_non_null} =
    let x, t = name.node, name.ty in
    let pp_t = pp_ity_non_null is_non_null in
    match in_rgn with
    | None -> fprintf out "@[%a:%a@]" pp_ident x pp_t t
    | Some e -> fprintf outf "@[%a:%a@ in@ %a@]" pp_ident x pp_t t pp_exp e in
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_qbind outf qbinds

  (* let pp_qbind out (x, eopt) =
   *   let (x, t) = x.node, x.ty in
   *   match eopt with
   *   | None -> fprintf out "@[%a:%a@]" pp_ident x pp_ity t
   *   | Some e -> fprintf out "@[%a:%a@ in@ %a@]" pp_ident x pp_ity t pp_exp e in
   * pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_qbind outf qbinds *)

let rec pp_formula' k outf f =
  match f with
  | Ftrue -> pp_print_string outf "True"
  | Ffalse -> pp_print_string outf "False"
  | Fexp e -> pp_exp outf e
  | Fnot f ->
    if k < (unrop_precedence Ast.Not)
    then fprintf outf "@[~(%a)@]" (pp_formula' 60) f
    else fprintf outf "@[~%a@]" (pp_formula' 60) f
  | Fpointsto (x, f, e) ->
    fprintf outf "@[%a.%a@ =@ %a@]" pp_ident x.node pp_ident f.node pp_exp e
  | Farray_pointsto (a, idx, e) ->
    fprintf outf "@[%a[%a]@,=@ %a@]" pp_ident a.node pp_exp idx pp_exp e
  | Fdisjoint (e1, e2) ->
    fprintf outf "@[%a@ #@ %a@]" (pp_exp' 70) e1 (pp_exp' 70) e2
  | Fsubseteq (e1, e2) ->
    fprintf outf "@[%a@ subset@ %a@]" (pp_exp' 70) e1 (pp_exp' 70) e2
  | Fmember (e1, e2) ->
    fprintf outf "@[%a@ in@ %a@]" pp_exp e1 pp_exp e2
  | Ftype (e1, tys) ->
    fprintf outf "@[Type(%a,@ %a)@]" pp_exp e1 pp_idents tys
  | Finit e -> fprintf outf "@[init(%a)@]" pp_let_bound_value e.node
  | Fold (e, lbv) ->
    fprintf outf "@[old(%a)@,=@ %a@]" pp_exp e pp_let_bound_value lbv.node
  | Flet (x, v, f) ->
    fprintf outf "@[let@ %a@ =@ %a@ in@;%a@]"
      pp_ident x.node pp_let_bind v.node pp_formula f
  | Fconn (c, f1, f2) ->
    let prec = connective_precedence c in
    let pp' = pp_formula' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' f1 pp_connective c pp' f2
    else fprintf outf "@[%a@ %a@ %a@]" pp' f1 pp_connective c pp' f2
  | Fquant (q, qbinds, frm) ->
    fprintf outf "@[<b 2>(%a@ %a.@ @[%a@])@]"
      pp_quantifier q pp_qbinders qbinds pp_formula frm

and pp_formula outf f = pp_formula' 0 outf f

let pp_atomic_command outf ac =
  match ac with
  | Skip -> fprintf outf "@[%s@]" "skip"
  | Assign (x, e) -> fprintf outf "@[%a@ :=@ %a@]" pp_ident x.node pp_exp e
  | Havoc x -> fprintf outf "@[havoc %a@]" pp_ident x.node
  | New_class (x, name) ->
    fprintf outf "@[%a@ :=@ new@ %a@]" pp_ident x.node pp_ident name
  | New_array (a, ty, len) ->
    fprintf outf "@[%a@ :=@ new(%a)[%a]@]" pp_ident a.node pp_ident ty pp_exp len
  | Field_deref (y, x, f) ->
    let y = y.node and x = x.node and f = f.node in
    fprintf outf "@[%a@ :=@ %a.%a@]" pp_ident y pp_ident x pp_ident f
  | Field_update (x, f, e) ->
    fprintf outf "@[%a.%a@ :=@ %a@]" pp_ident x.node pp_ident f.node pp_exp e
  | Array_access (x, a, e) ->
    fprintf outf "@[%a@ :=@ %a[%a]@]" pp_ident x.node pp_ident a.node pp_exp e
  | Array_update (a, e1, e2) ->
    fprintf outf "@[%a[%a]@ :=@ %a@]" pp_ident a.node pp_exp e1 pp_exp e2
  | Call (x, meth, args) ->
    fprintf outf "@[%s%a(%a)@]"
      (match x with
       | Some id -> Astutil.string_of_ident id.node ^ " := "
       | None -> "")
      pp_ident meth.node
      pp_idents (List.map (fun e -> e.node) args)

let pp_atomic_command_special outf ac =
  match ac with
  | New_array (a, ty,  len) ->
    fprintf outf "@[%a@ :=@ new(%a){%a}@]"
      pp_ident a.node pp_ident ty pp_exp len
  | Array_access (x, a, e) ->
    fprintf outf "@[%a@ :=@ %a.{%a}@]"
      pp_ident x.node pp_ident a.node pp_exp e
  | Array_update (a, e1, e2) ->
    fprintf outf "@[%a.{%a}@ :=@ %a@]"
      pp_ident a.node pp_exp e1 pp_exp e2
  | _ -> pp_atomic_command outf ac

let pp_effect_kind outf = function
  | Ast.Read -> fprintf outf "rd"
  | Ast.Write -> fprintf outf "wr"

let pp_effect_desc outf = function
  | Effvar id -> pp_ident outf id.node
  | Effimg (g, f) -> let exp = Eimage (g, f) -: Trgn in pp_exp outf exp

let pp_effect_elt outf {effect_kind; effect_desc=desc} =
  fprintf outf "@[%a@ %a@]" pp_effect_kind effect_kind pp_effect_desc desc.node

let pp_effect' outf eff =
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ";@;") pp_effect_elt outf eff

let pp_effect outf eff = fprintf outf "@[%a@]" pp_effect' eff

let rec pp_value_in_state outf = function
  | Left e -> fprintf outf "@[[<%a<]@]" pp_exp e
  | Right e -> fprintf outf "@[[<%a<]@]"pp_exp e

let rec pp_biexp' k outf b =
  match b.node with
  | Biconst c -> fprintf outf "@[[%a]@]" pp_const_exp c.node
  | Bivalue v -> pp_value_in_state outf v.node
  | Bibinop (op, e1, e2) ->
    let prec = binop_precedence op in
    let pp' = pp_biexp' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' e1 pp_binop op pp' e2
    else fprintf outf "@[%a@ %a@ %a@]" pp' e1 pp_binop op pp' e2

let rec pp_rformula' k outf rfrm =
  let open List in
  match rfrm with
  | Rprimitive {name=fn; left_args=l; right_args=r} ->
    fprintf outf "@[%a@,(@[%a@]@ |@ @[%a@])@]" pp_ident fn pp_exps l pp_exps r
  | Rbiexp b -> pp_biexp' 0 outf b
  | Rnot rf ->
    if k > (unrop_precedence Ast.Not)
    then fprintf outf "@[~(%a)@]" (pp_rformula' 60) rf
    else fprintf outf "@[~%a@]" (pp_rformula' 60) rf
  | Rbiequal (e1, e2) ->
    begin match e1.node, e2.node with
      | Evar x, Evar y when x.node = y.node && e1.ty = e2.ty && x.ty = y.ty ->
        fprintf outf "@[Agree@ %a@]" pp_ident x.node
      | _ -> fprintf outf "@[%a@ =:=@ %a@]" pp_exp e1 pp_exp e2
    end
  | Ragree (g, f) ->
    fprintf outf "@[Agree@ %a`%a@]" (pp_exp' 70) g
      pp_ident f.node
  | Rboth f -> fprintf outf "@[Both@ (%a)@]" pp_formula f
  | Rleft f -> fprintf outf "@[<|@ %a@ <]@]" pp_formula f
  | Rright f -> fprintf outf "@[[>@ %a@ |>@]" pp_formula f
  | Rconn (c, rf1, rf2) ->
    let prec = connective_precedence c in
    let pp' = pp_rformula' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' rf1 pp_connective c pp' rf2
    else fprintf outf "@[%a@ %a@ %a@]" pp' rf1 pp_connective c pp' rf2
  | Rlet (Some (lid, lty, lval), Some (rid, rty, rval), rf) ->
    fprintf outf "@[let@ %a@ |@ %a@ =@ %a@ |@ %a@ in@;%a@]"
      pp_ident lid.node pp_ident rid.node
      pp_let_bind lval.node pp_let_bind rval.node
      pp_rformula rf
  | Rlet (Some (lid, lty, lval), None, rf) ->
    fprintf outf "@[let@ %a@ |@ =@ %a@ in@;%a@]"
      pp_ident lid.node
      pp_let_bind lval.node
      pp_rformula rf
  | Rlet (None, Some (rid, rty, rval), rf) ->
    fprintf outf "@[let@ |@ %a@ =@ %a@ in@;%a@]"
      pp_ident rid.node
      pp_let_bind rval.node
      pp_rformula rf
  | Rlet (None, None, _) -> assert false (* impossible *)
  | Rquant (q, (lbinds, rbinds), rfrm) ->
    fprintf outf "@[<b 2>(%a@ %a@ |@ %a.@ @[%a@])@]"
      pp_quantifier q pp_qbinders lbinds pp_qbinders rbinds pp_rformula rfrm
  | Rlater rf ->
    fprintf outf "@[ <>(%a)@]" pp_rformula rf

and pp_rformula outf f = pp_rformula' 0 outf f

let pp_bispec outf bispec =
  List.iter (function
      | Bieffects (e, e') ->
        fprintf outf "@[effects  @[{@[<h 2>@ %a@]@;|@[<h 2>@ %a@,@] }@]\n@]"
          pp_effect e pp_effect e'
      | Biprecond f ->
        fprintf outf "@[requires@ {@[<h 2>@ %a@ @]}@\n@]"
          pp_rformula f
      | Bipostcond f ->
        fprintf outf "@[ensures  {@[<h 2>@ %a@ @]}@\n@]"
          pp_rformula f
    ) bispec

let rec pp_command' outf c = match c with
  | Acommand ac -> pp_atomic_command outf ac
  | Vardecl (x, Some m, ty, c) ->
    fprintf outf "@[var@ %a@ %a@ :@ %a@ in@.@[%a@]@]"
      pp_modifier m pp_ident x.node pp_ity ty pp_command' c
  | Vardecl (x, None, ty, c) ->
    fprintf outf "@[var@ %a@ :@ %a@ in@.@[<hov 2>%a@]@]"
      pp_ident x.node pp_ity ty pp_command' c
  | Seq (c1, c2) -> fprintf outf "@[%a;@.%a@]" pp_command' c1 pp_command' c2
  | If (e, c1, c2) ->
    fprintf outf "@[if@ %a@;then@ %a@.else@ @[<hv 1>%a@]@ end@]"
      pp_exp e pp_command' c1 pp_command' c2
  | While (e, inv, c) ->
    fprintf outf
      "@[while@ %a@ do@.@[<b 2>%a@]@.@[<b 2>%a@]@.done@]"
      pp_exp e pp_while_spec inv pp_command' c
  | Assume f -> fprintf outf "@[assume@ {%a}@]" pp_formula f
  | Assert f -> fprintf outf "@[assert@ {%a}@]" pp_formula f

and pp_while_spec outf {winvariants; wframe} =
  let rec print_invariants invs = match invs with
    | [] -> ()
    | f :: fs ->
      fprintf outf "@[invariant @<v 2>[{%a}@] @]" pp_formula f;
      print_invariants fs
  in
  print_invariants winvariants; pp_effect outf wframe

and pp_modifier outf = function
  | Ast.Ghost -> fprintf outf "ghost"
  | Ast.Public -> ()
  | Ast.Modscope -> fprintf outf "modscope"

and pp_modifier_opt outf = function
  | Some modif -> pp_modifier outf modif
  | None -> ()

and pp_command outf c =
  let old_margin = get_margin () and old_indent = get_max_indent () in
  set_margin 10; set_max_indent 6;
  fprintf outf "@[<v 2>%a@]" pp_command' c;
  set_margin old_margin; set_max_indent old_indent


(** locEq.ml -- derive local equivalence specs *)

open Astutil
open Annot
open Lib

exception Unknown_method of string

let both_precondition = map (fun f -> Biprecond (Rboth f))

let both_postcondition = map (fun f -> Bipostcond (Rboth f))

let rec eff_contains_any (eff: effect) =
  let is_any = function
    | {effect_desc = {node = Effimg(g,f)}} -> f.node = Id "any"
    | _ -> false in
  exists is_any eff

let local_equivalence bnd spec =
  let pre, post = fork (spec_preconds, spec_postconds) spec in
  let eff = Norm.normalize (spec_effects spec) in
  assert (not (eff_contains_any (eff_of_bnd bnd)));
  assert (not (eff_contains_any eff));
  let agree_pre = agreement_effpre eff bnd in
  let agree_post = agreement_effpost eff bnd in
  let bi_pre = both_precondition pre @ map mk_bispec_pre agree_pre in
  let bi_post = both_postcondition post @ [mk_bispec_post agree_post] in
  bi_pre @ bi_post @ [Bieffects (eff,eff)]

let rec derive_locEq penv meth_name =
  let mdl, intr = find_method_interface_and_module penv meth_name in
  (* [Sep-30-22] Previously used Boundary_info.imported_boundaries, but this
     leads to agreements in the post that aren't provable.  We need to
     subtract the current boundary from the agreement_effpost of spec.  *)
  let bnd = Boundary_info.overall_boundary mdl in
  let spec = find_method_spec penv (mdl, intr) meth_name in
  local_equivalence bnd spec

and find_method_interface_and_module penv meth_name : ident * ident =
  let res = ref None in
  let find _ = function
    | Unary_module m when mem meth_name (module_methods m) ->
      res := Some (m.mdl_name, m.mdl_interface)
    | _ -> () in
  M.iter find penv;
  try Option.get !res with _ ->
    raise (Unknown_method (string_of_ident meth_name))

and find_method_spec penv (mdl_name, intr_name) meth_name : spec =
  let mdl = find_unary_module penv mdl_name in
  let intr = find_unary_interface penv intr_name in
  let intr_meths = interface_methods intr in
  if mem meth_name intr_meths then find_spec_in_interface intr meth_name
  else find_spec_in_module mdl meth_name

and find_spec_in_interface intr meth_name : spec =
  let find = function
    | Intr_mdecl m when m.meth_name.node = meth_name -> Some m.meth_spec
    | _ -> None
  in first find intr.intr_elts

and find_spec_in_module mdl meth_name : spec =
  let find = function
    | Mdl_mdef (Method (m, _)) when m.meth_name.node = meth_name ->
      Some m.meth_spec
    | _ -> None
  in first find mdl.mdl_elts

let pp_derive_locEq penv meth_name outf : unit =
  let loc_eq = derive_locEq penv meth_name in
  Pretty.pp_bispec outf loc_eq

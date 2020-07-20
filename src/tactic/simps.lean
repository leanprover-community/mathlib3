/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core
/-!
# simps attribute

This file defines the `@[simps]` attribute, to automatically generate simp-lemmas
reducing a definition when projections are applied to it.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

open tactic expr

setup_tactic_parser
@[derive has_reflect] structure simps_cfg :=
-- give the generated lemmas the `@[simp]` attribute
(simp_attr    := tt)
-- give the generated lemmas a shorter name
(short_name    := ff)
-- simplify the right-hand-side of the simp lemmas
(simp_rhs      := ff)

/--
The `@[simps_str]` specifies the projections of the given structure, using by the `@[simps]
attribute.
- This will usually be tagged by the `@[simps]` tactic.
- If you specify it yourself, make sure it is specified in the same file as the structure
  declaration.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is the expressions that correspond to the projections of the structure
  (these can contain the universe parameters specified in the first argument).
-/
@[user_attribute] meta def simps_str_attr : user_attribute unit (list name × list expr) :=
{ name := `simps_str,
  descr := "An attribute specifying the projection of the given structure.",
  parser := do e ← texpr, eval_pexpr _ e }

declare_trace simps.verbose

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables.
  If `add_simp` then we make the resulting lemma a simp-lemma. -/
meta def simps_add_projection (nm : name) (type lhs rhs : expr) (args : list expr)
  (univs : list name) (cfg : simps_cfg) : tactic unit := do
  rhs ← if cfg.simp_rhs then return rhs else return rhs, -- TODO
  eq_ap ← mk_mapp `eq $ [type, lhs, rhs].map some,
  refl_ap ← mk_app `eq.refl [type, lhs],
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := refl_ap.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  when_tracing `simps.verbose trace!"[simps] > adding projection\n        > {decl_name} : {decl_type}",
  add_decl decl <|> fail format!"failed to add projection lemma {decl_name}.",
  when cfg.simp_attr $ do
    set_basic_attribute `_refl_lemma decl_name tt,
    set_basic_attribute `simp decl_name tt

meta def simps_decls : list (bool × name × name) :=
[(ff, `has_coe_to_sort, `coe_sort), (ff, `has_coe_to_fun, `coe_fn), (tt, `has_mul, `has_mul.mul)]

/- finds an instance of an implication `cond → tgt`. -/
meta def mk_conditional_instance (cond tgt : expr) : tactic (expr × expr) := do
f ← mk_meta_var cond,
e ← assertv `c cond f, swap,
reset_instance_cache,
inst ← mk_instance tgt,
-- trace $ pformat!"({e} : {infer_type e})",
-- trace $ pformat!"({inst} : {infer_type inst})",
-- trace $ pformat!"({inst.bind_lambda e} : {infer_type $ inst.bind_lambda e})",
return (e, inst)

/-- Get the projections used by `simps` associated to a given structure. -/
meta def simps_get_raw_projections (e : environment) (str : name) :
  tactic (list name × list expr) := do
  has_attr ← has_attribute' `simps_str str,
  if has_attr then do
    when_tracing `simps.verbose trace!"[simps] > found projection information for structure {str}",
    simps_str_attr.get_param str
  else do
    when_tracing `simps.verbose trace!"[simps] > generating projection information to structure {str}:",
    d_str ← e.get str,
    projs ← e.structure_fields_full str,
    (args, _) ← mk_local_pis d_str.type,
    let raw_univs := d_str.univ_params,
    let raw_levels := level.param <$> raw_univs,
    let raw_exprs : list expr := projs.map $ λ proj, (expr.const proj raw_levels),
    /- check for other coercions and type-class arguments to use as projections instead. -/
    let e_str := (expr.const str raw_levels).mk_app args,
    raw_exprs ← simps_decls.mfoldl (λ (raw_exprs : list expr) ⟨is_class, class_nm, proj_nm⟩, (do
      (raw_expr, lambda_raw_expr) ← if is_class then (do failed -- todo
        /-let e_inst_type := (expr.const class_nm raw_levels).mk_app args,
        -- trace e_inst_type.to_string,
        (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type),
        -- trace e_inst.to_string,
        -- t_inst ← infer_type e_inst,
        -- trace t_inst.to_string,

        -- trace e_str.to_string,
        -- trace e_inst.to_string,
        raw_expr ← mk_mapp proj_nm [args.head, e_inst],
        return (raw_expr, (raw_expr.bind_lambda hyp).lambdas args)-/)
      else (do
        e_inst_type ← to_expr ((expr.const class_nm []).app (pexpr.of_expr e_str)),
        -- trace e_inst_type.to_string,
        e_inst ← try_for 1000 (mk_instance e_inst_type),
        -- trace e_inst.to_string,
        raw_expr ← mk_mapp proj_nm [e_str, e_inst],
        return (raw_expr, raw_expr.lambdas args)),
      trace raw_expr.to_string,
      infer_type raw_expr >>= trace,
      raw_expr_whnf ← whnf raw_expr.binding_body,
      trace raw_expr_whnf.to_string,
      let relevant_proj := raw_expr_whnf.get_app_fn.const_name,
      guard (projs.any (= relevant_proj)),
      let pos := projs.find_index (= relevant_proj),
      return $ raw_exprs.update_nth pos lambda_raw_expr) <|> return raw_exprs) raw_exprs,
    when_tracing `simps.verbose trace!"[simps] > {raw_exprs}",
    when_tracing `simps.verbose trace!"[simps] > {raw_exprs.map expr.to_string}",
    simps_str_attr.set str (raw_univs, raw_exprs) tt,
    return (raw_univs, raw_exprs)

/-- Get the projections of a structure used by simps applied to the appropriate arguments.
  Returns a list of triples (projection expression, projection name, corresponding right-hand-side).

  This function does not use `tactic.mk_app` or `tactic.mk_mapp`, because the the given arguments
  might not uniquely specify the universe levels yet.
 -/
meta def simps_get_projection_exprs (e : environment) (tgt : expr)
  (rhs : expr) : tactic $ list $ expr × name × expr := do
  let params := get_app_args tgt, -- the parameters of the structure
  guard ((get_app_args rhs).take params.length = params) <|> fail "unreachable code (1)",
  let str := tgt.get_app_fn.const_name,
  projs ← e.structure_fields_full str,
  let rhs_args := (get_app_args rhs).drop params.length, -- the fields of the structure
  guard (rhs_args.length = projs.length) <|> fail "unreachable code (2)",
  (raw_univs, raw_exprs) ← simps_get_raw_projections e str,
  let univs := raw_univs.zip tgt.get_app_fn.univ_levels,
  let proj_exprs := raw_exprs.map $
    λ raw_expr, (raw_expr.instantiate_univ_params univs).substs params,
  return $ proj_exprs.zip $ projs.zip rhs_args

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`. -/
meta def simps_add_projections : ∀(e : environment) (nm : name) (suffix : string)
  (type lhs rhs : expr) (args : list expr) (univs : list name) (must_be_str : bool)
  (cfg : simps_cfg) (todo : list string), tactic unit
| e nm suffix type lhs rhs args univs must_be_str cfg todo := do
  (type_args, tgt) ← mk_local_pis_whnf type,
  tgt ← whnf tgt,
  let new_args := args ++ type_args,
  let lhs_ap := lhs.mk_app type_args,
  let rhs_ap := rhs.instantiate_lambdas_or_apps type_args,
  let str := tgt.get_app_fn.const_name,
  /- Don't recursively continue if `str` is not a structure. As a special case, also don't
    recursively continue if the nested structure is `prod` or `pprod`, unless projections are
    specified manually. -/
  if e.is_structure str ∧ ¬(todo = [] ∧ str ∈ [`prod, `pprod] ∧ ¬must_be_str) then do
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    if is_constant_of (get_app_fn rhs_ap) intro then do -- if the value is a constructor application
      tuples ← simps_get_projection_exprs e tgt rhs_ap,
      let projs := tuples.map $ λ x, x.2.1,
      let pairs := tuples.map $ λ x, x.2,
      eta ← expr.is_eta_expansion_aux rhs_ap pairs, -- check whether `rhs_ap` is an eta-expansion
      let rhs_ap := eta.lhoare rhs_ap, -- eta-reduce `rhs_ap`
      /- we want to generate the current projection if it is in `todo` or when `rhs_ap` was an
      eta-expansion -/
      when ("" ∈ todo ∨ (todo = [] ∧ eta.is_some)) $
        simps_add_projection (nm.append_suffix suffix) tgt lhs_ap rhs_ap new_args univs cfg,
      -- if `rhs_ap` was an eta-expansion and `todo` is empty, we stop
      when ¬(todo = [""] ∨ (eta.is_some ∧ todo = [])) $ do
        /- remove "" from todo. This allows a to generate lemmas + nested version of them.
          This is not very useful, but this does improve error messages. -/
        let todo := todo.filter $ (≠ ""),
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).is_prefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).is_prefix_of x).iget,
            simp_lemma := nm.append_suffix $ suffix ++ x,
            needed_proj := (x.split_on '_').tail.head in
          fail format!"Invalid simp-lemma {simp_lemma}. Projection {needed_proj} doesn't exist.",
        tuples.mmap' $ λ ⟨proj_expr, proj, new_rhs⟩, do
          new_type ← infer_type new_rhs,
          let new_todo := todo.filter_map $ λ x, string.get_rest x $ "_" ++ proj.last,
          b ← is_prop new_type,
          -- we only continue with this field if it is non-propositional or mentioned in todo
          when ((¬ b ∧ todo = []) ∨ (todo ≠ [] ∧ new_todo ≠ [])) $ do
            let new_lhs := proj_expr.app lhs_ap,
            let new_suffix := if cfg.short_name then "_" ++ proj.last else
              suffix ++ "_" ++ proj.last,
            simps_add_projections e nm new_suffix new_type new_lhs new_rhs new_args univs
              ff cfg new_todo
    else do
      when must_be_str $
        fail "Invalid `simps` attribute. Body is not a constructor application",
      when (todo ≠ [] ∧ todo ≠ [""]) $
        fail format!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo.head}. The given definition is not a constructor application.",
      simps_add_projection (nm.append_suffix suffix) tgt lhs_ap rhs_ap new_args univs cfg
  else do
    when must_be_str $
      fail "Invalid `simps` attribute. Target is not a structure",
    when (todo ≠ [] ∧ todo ≠ [""] ∧ str ∉ [`prod, `pprod]) $
        fail format!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo.head}. Projection {(todo.head.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    simps_add_projection (nm.append_suffix suffix) tgt lhs_ap rhs_ap new_args univs cfg

/-- `simps_tac` derives simp-lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name. -/
meta def simps_tac (nm : name) (cfg : simps_cfg := {}) (todo : list string := []) : tactic unit := do
  e ← get_env,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  let todo := todo.erase_dup.map $ λ proj, "_" ++ proj,
  simps_add_projections e nm "" d.type lhs d.value [] d.univ_params tt cfg todo

/-- The parser for the `@[simps]` attribute. -/
meta def simps_parser : parser (list string × simps_cfg) := do
/- note: we currently don't check whether the user has written a nonsense namespace as arguments. -/
prod.mk <$> many (name.last <$> ident) <*>
  ((do e ← parser.pexpr, eval_pexpr simps_cfg e) <|> return {})

/--
The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example: (note that the forward and reverse functions are specified differently!)
```lean
@[simps] def refl (α) : α ≃ α := ⟨id, λ x, x, λ x, rfl, λ x, rfl⟩
```
derives two simp-lemmas:
```lean
@[simp] lemma refl_to_fun (α) (x : α) : (refl α).to_fun x = id x
@[simp] lemma refl_inv_fun (α) (x : α) : (refl α).inv_fun x = x
```

* It does not derive simp-lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
  * Exception: by default it will not recursively create simp-lemmas for fields in the structures
    `prod` and `pprod`. Give explicit projection names to override this.
* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections. For example:
  ```lean
  attribute [simps to_fun] refl
  ```
  * Recursive projection names can be specified using `foo_proj1_proj2_proj3`.
    This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.
* You can use `@[simps {simp_attr := ff}]` to derive the lemmas, but not mark them
  as simp-lemmas.
* You can use `@[simps {short_name := tt}]` to only use the name of the last projection
  for the name of the generated lemmas.
* The precise syntax is `('simps' ident* e)`, where `e` is an expression of type `simps_cfg`.
* If one of the projections is marked as a coercion, the generated lemmas do *not* use this
  coercion.
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
* When option `trace.simps.verbose` is true, `simps` will print the name and type of the
  lemmas it generates.

  -/
@[user_attribute] meta def simps_attr : user_attribute unit (list string × simps_cfg) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simps_parser,
  after_set := some $
    λ n _ _, do (todo, cfg) ← simps_attr.get_param n, simps_tac n cfg todo }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  decl_names               := [`simps_attr],
  tags                     := ["simplification"] }

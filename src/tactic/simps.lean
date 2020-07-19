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

declare_trace simps.verbose

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables.
  If `add_simp` then we make the resulting lemma a simp-lemma. -/
meta def simps_add_projection (nm : name) (type lhs rhs : expr) (args : list expr)
  (univs : list name) (add_simp : bool) : tactic unit := do
  eq_ap ← mk_mapp `eq $ [type, lhs, rhs].map some,
  refl_ap ← mk_app `eq.refl [type, lhs],
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := refl_ap.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  add_decl decl <|> fail format!"failed to add projection lemma {decl_name}.",
  when_tracing `simps.verbose trace!"[simps] > adding projection\n        > {decl_name} : {decl_type}",
  when add_simp $ do
    set_basic_attribute `_refl_lemma decl_name tt,
    set_basic_attribute `simp decl_name tt

/-- Get the projections of a structure used by simps. Returns a list of triples
  (projection expression, projection name, corresponding right-hand-side) -/
meta def simps_get_projection_exprs (e : environment) (tgt : expr)
  (rhs : expr) : tactic $ list $ expr × name × expr := do
  let str := tgt.get_app_fn.const_name,
  let params := get_app_args tgt, -- the parameters of the structure
  let univ_levels := tgt.get_app_fn.univ_levels, -- the universe arguments of the structure
  projs ← e.structure_fields_full str,
  guard ((get_app_args rhs).take params.length = params) <|> fail "unreachable code (1)",
  let rhs_args := (get_app_args rhs).drop params.length, -- the fields of the structure
  guard (rhs_args.length = projs.length) <|> fail "unreachable code (2)",
  -- cannot use `tactic.mk_app` here, since the resulting application is still a function.
  -- cannot use `tactic.mk_mapp` here, since the the given arguments here might not uniquely
  -- specify the universe levels.
  let proj_exprs := projs.map $ λ proj, (expr.const proj univ_levels).mk_app params,
  return $ proj_exprs.zip $ projs.zip rhs_args

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`. -/
meta def simps_add_projections : ∀(e : environment) (nm : name) (suffix : string)
  (type lhs rhs : expr) (args : list expr) (univs : list name)
  (add_simp must_be_str short_nm : bool) (todo : list string), tactic unit
| e nm suffix type lhs rhs args univs add_simp must_be_str short_nm todo := do
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
        simps_add_projection (nm.append_suffix suffix) tgt lhs_ap rhs_ap new_args univs add_simp,
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
            let new_suffix := if short_nm then "_" ++ proj.last else
              suffix ++ "_" ++ proj.last,
            simps_add_projections e nm new_suffix new_type new_lhs new_rhs new_args univs
              add_simp ff short_nm new_todo
    else do
      when must_be_str $
        fail "Invalid `simps` attribute. Body is not a constructor application",
      when (todo ≠ [] ∧ todo ≠ [""]) $
        fail format!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo.head}. The given definition is not a constructor application.",
      simps_add_projection (nm.append_suffix suffix) tgt lhs_ap rhs_ap new_args univs add_simp
  else do
    when must_be_str $
      fail "Invalid `simps` attribute. Target is not a structure",
    when (todo ≠ [] ∧ todo ≠ [""] ∧ str ∉ [`prod, `pprod]) $
        fail format!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo.head}. Projection {(todo.head.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    simps_add_projection (nm.append_suffix suffix) tgt lhs_ap rhs_ap new_args univs add_simp

/-- `simps_tac` derives simp-lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name. -/
meta def simps_tac (nm : name) (add_simp : bool) (short_nm : bool := ff)
  (todo : list string := []) : tactic unit := do
  e ← get_env,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  let todo := todo.erase_dup.map $ λ proj, "_" ++ proj,
  simps_add_projections e nm "" d.type lhs d.value [] d.univ_params add_simp tt short_nm todo

reserve notation `lemmas_only`
reserve notation `short_name`
setup_tactic_parser

/-- The parser for simps. Pattern: `'lemmas_only'? 'short_name'? ident*` -/
meta def simps_parser : parser (bool × bool × list string) :=
/- note: we currently don't check whether the user has written a nonsense namespace as arguments. -/
prod.mk <$> (option.is_none <$> (tk "lemmas_only")?) <*>
(prod.mk <$> (option.is_some <$> (tk "short_name")?) <*> many (name.last <$> ident))


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
* It will automatically reduce newly created beta-redexes, but not unfold any definitions.
* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
  * Exception: by default it will not recursively create simp-lemmas for fields in the structures
    `prod` and `pprod`. Give explicit projection names to override this.
* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections. For example:
  ```lean
  attribute [simps to_fun] refl
  ```
  * Recursive projection names can be specified using `foo_proj1_proj2_proj3`. This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.
* You can use `@[simps lemmas_only]` to derive the lemmas, but not mark them
  as simp-lemmas.
* You can use `@[simps short_name]` to only use the name of the last projection for the name of the
  generated lemmas.
* The precise syntax is `('simps' 'lemmas_only'? 'short_name'? ident*)`.
* If one of the projections is marked as a coercion, the generated lemmas do *not* use this
  coercion.
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
* When option `trace.simps.verbose` is true, `simps` will print the name and type of the
  lemmas it generates.

  -/
@[user_attribute] meta def simps_attr : user_attribute unit (bool × bool × list string) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simps_parser,
  after_set := some $
    λ n _ _, do (add_simp, short_nm, todo) ← simps_attr.get_param n,
      simps_tac n add_simp short_nm todo }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  decl_names               := [`simps_attr],
  tags                     := ["simplification"] }

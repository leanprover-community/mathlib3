/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core
/-!
  # reduce_projections attribute
  This file defines the `@[reduce_projections]` attribute, to automatically generate simp-lemmas
  reducing a definition when projections are applied to it.

  ## Tags
  structures, projections, simp, simplifier, generates declarations
-/

open tactic expr

/- Add a lemma stating that the projection `proj` (with parameters `params`) applied to
  "`d` applied to `args`" is equal to `value`. Makes it a simp-lemma if `add_simp` is `tt`. -/
meta def add_projection_decl (d : declaration) (proj : name) (value : expr)
  (args params : list expr) (add_simp : bool) :
  tactic unit := do
value_type ← infer_type value,
    b ← is_prop value_type,
    when ¬ b $ do
      decl_ap ← mk_app d.to_name args,
      -- cannot use `mk_app` here, since the resulting application might still be a function.
      proj_ap ← mk_mapp proj $ (params ++ [decl_ap]).map some,
      eq_ap ← mk_app `eq [value_type, proj_ap, value],
      refl_ap ← mk_app `eq.refl [value_type, value],
      let decl_name := d.to_name.append_suffix $ "_" ++ proj.last,
      let decl_type := eq_ap.pis args,
      let decl_value := refl_ap.lambdas args,
      let decl := declaration.thm decl_name d.univ_params decl_type (pure decl_value),
      add_decl decl <|> fail format!"failed to add projection lemma for {proj}",
      when add_simp $ set_basic_attribute `simp decl_name

/-- Derive lemmas specifying the projections of the declaration. -/
meta def reduce_projections_tac (n : name) (add_simp : bool) : tactic unit := do
  e ← get_env,
  d ← e.get n,
  (args, tgt) ← mk_local_pis d.type,
  const str _ ← return tgt.get_app_fn,
    when (¬ e.is_structure str) $
    fail "Invalid `reduce_projections` attribute. Target is not a structure",
  projs ← e.get_projections str,
  [intro] ← return $ e.constructors_of str,
  let params := get_app_args tgt,
  let val := d.value.instantiate_lambdas args,
  when (¬ is_constant_of (get_app_fn val) intro) $
    fail "Invalid `reduce_projections` attribute. Body is not a constructor application",
  guard ((get_app_args val).take params.length = params) <|> fail "unreachable code (1)",
  let values := (get_app_args val).drop params.length,
  guard (values.length = projs.length) <|> fail "unreachable code (2)",
  (projs.zip values).mmap' $ λ ⟨proj, value⟩, add_projection_decl d proj value args params add_simp

reserve notation `no_simp`
setup_tactic_parser

/-- Automatically derive lemmas specifying the projections of this declaration.
  Example:
  ```
  @[reduce_projections] def refl (α) : α ≃ α := ⟨id, id, λ x, rfl, λ x, rfl⟩
  ```
  derives two simp-lemmas:
  ```
  @[simp] lemma refl_to_fun (α) : (refl α).to_fun = id
  @[simp] lemma refl_inv_fun (α) : (refl α).inv_fun = id
  ```
  It does not derive simp-lemmas for the prop-valued projections.

  You can use `@[reduce_projections no_simp]` to derive the lemmas, but not mark them as simp-lemmas.

  If one of the projections is marked as a coercion, the generated lemmas do *not* use this coercion.
  -/
@[user_attribute] meta def reduce_projections_attr : user_attribute unit (option unit) :=
{ name := `reduce_projections,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := optional (tk "no_simp"),
  after_set := some $
    λ n _ _, option.is_none <$> reduce_projections_attr.get_param n >>= reduce_projections_tac n }

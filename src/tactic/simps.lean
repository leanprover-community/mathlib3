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

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables.
  If `add_simp` then we make the resulting lemma a simp-lemma. -/
meta def add_projection (nm : name) (type lhs rhs : expr) (args : list expr)
  (univs : list name) (add_simp : bool) : tactic unit := do
  eq_ap ← mk_mapp `eq $ [type, lhs, rhs].map some,
  refl_ap ← mk_app `eq.refl [type, lhs],
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := refl_ap.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  add_decl decl <|> fail format!"failed to add projection lemma {decl_name}.",
  when add_simp $
    set_basic_attribute `simp decl_name tt >> set_basic_attribute `_refl_lemma decl_name tt

/-- Derive lemmas specifying the projections of the declaration. -/
meta def add_projections : ∀(e : environment) (nm : name) (type lhs rhs : expr)
  (args : list expr) (univs : list name) (add_simp must_be_str : bool), tactic unit
  | e nm type lhs rhs args univs add_simp must_be_str := do
  (type_args, tgt) ← mk_local_pis_whnf type,
  tgt ← whnf tgt,
  let new_args := args ++ type_args,
  let lhs_ap := lhs.mk_app type_args,
  let rhs_ap := rhs.instantiate_lambdas_or_apps type_args,
  let str := tgt.get_app_fn.const_name,
  if e.is_structure str then do
    projs ← e.get_projections str,
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    let params := get_app_args tgt, -- the parameters of the structure
    if is_constant_of (get_app_fn rhs_ap) intro then do -- if the value is a constructor application
      guard ((get_app_args rhs_ap).take params.length = params) <|> fail "unreachable code (1)",
      let rhs_args := (get_app_args rhs_ap).drop params.length, -- the fields of the structure
      guard (rhs_args.length = projs.length) <|> fail "unreachable code (2)",
      let pairs := projs.zip rhs_args,
      eta ← expr.is_eta_expansion_aux rhs_ap pairs,
      match eta with
      | none                 :=
        pairs.mmap' $ λ ⟨proj, new_rhs⟩, do
          new_type ← infer_type new_rhs,
          b ← is_prop new_type,
          when ¬ b $ do -- if this field is a proposition, we skip it
            -- cannot use `mk_app` here, since the resulting application might still be a function.
            new_lhs ← mk_mapp proj $ (params ++ [lhs_ap]).map some,
            let new_nm := nm.append_suffix $ "_" ++ proj.last,
            add_projections e new_nm new_type new_lhs new_rhs new_args univs add_simp ff
      | (some eta_reduction) := add_projection nm tgt lhs_ap eta_reduction new_args univs add_simp
      end
    else (do
      when must_be_str $
        fail "Invalid `simps` attribute. Body is not a constructor application",
      add_projection nm tgt lhs_ap rhs_ap new_args univs add_simp)
  else
    (do when must_be_str $
      fail "Invalid `simps` attribute. Target is not a structure",
    add_projection nm tgt lhs_ap rhs_ap new_args univs add_simp)

/-- Derive lemmas specifying the projections of the declaration. -/
meta def simps_tac (nm : name) (add_simp : bool) : tactic unit := do
  e ← get_env,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  add_projections e nm d.type lhs d.value [] d.univ_params add_simp tt

reserve notation `lemmas_only`
setup_tactic_parser

/-- Automatically derive lemmas specifying the projections of this declaration.
  Example: (note that the forward and reverse functions are specified differently!)
  ```
  @[simps] def refl (α) : α ≃ α := ⟨id, λ x, x, λ x, rfl, λ x, rfl⟩
  ```
  derives two simp-lemmas:
  ```
  @[simp] lemma refl_to_fun (α) (x : α) : (refl α).to_fun x = id x
  @[simp] lemma refl_inv_fun (α) (x : α) : (refl α).inv_fun x = x
  ```
  * It does not derive simp-lemmas for the prop-valued projections.
  * It will automatically reduce newly created beta-redexes, but not unfold any definitions.
  * If one of the fields itself is a structure, this command will recursively create
    simp-lemmas for all fields in that structure.
  * If one of the values is an eta-expanded structure, we will eta-reduce this structure.
  * You can use `@[simps lemmas_only]` to derive the lemmas, but not mark them
    as simp-lemmas.
  * If one of the projections is marked as a coercion, the generated lemmas do *not* use this
    coercion.
  * If one of the fields is a partially applied constructor, we will eta-expand it
    (this likely never happens).
  -/
@[user_attribute] meta def simps_attr : user_attribute unit (option unit) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := optional (tk "lemmas_only"),
  after_set := some $
    λ n _ _, option.is_none <$> simps_attr.get_param n >>= simps_tac n }

/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core category.traversable.basic tactic.replacer
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
meta def simps_add_projection (nm : name) (type lhs rhs pr : expr) (args : list expr)
  (univs : list name) (add_simp : bool) : tactic unit :=
do eq_ap ← mk_mapp `eq [type, lhs, rhs],
   decl_name ← get_unused_decl_name nm,
   let decl_type := eq_ap.pis args,
   decl_type ← instantiate_mvars decl_type,
   decl_value ← instantiate_mvars pr,
   when_tracing `simps_lemmas_names $ trace!"New lemma: {decl_name} : {decl_type}",
   let decl := declaration.thm decl_name univs decl_type (pure decl_value),
   trace_error (sformat!"failed to add projection lemma {decl_name}.") $ add_decl decl,
   when add_simp $
     set_basic_attribute `simp decl_name tt >> set_basic_attribute `_refl_lemma decl_name tt

meta def simps_add_projection' (nm : name) (type lhs rhs : expr) (pr : option expr) (args : list expr)
  (univs : list name) (add_simp : bool) : tactic unit :=
do decl_value ← match pr with
                | none := mk_app `eq.refl [type, lhs]
                | (some pr) := pure pr
                end,
   let decl_value := decl_value.lambdas args,
   simps_add_projection nm type lhs rhs decl_value args univs add_simp

open native

@[user_attribute]
meta def projection_attr : user_attribute (rb_lmap name (name × name)) name :=
{ name := `projection,
  descr := "descr",
  cache_cfg := { mk_cache := λ ls,
                 do { ls.mfoldl (λ m l,
                       do d ← projection_attr.get_param l,
                          decl ← get_decl l,
                          (_,t) ← mk_local_pis decl.type,
                          (lhs,rhs) ← match_eq t,
                          pure $ m.insert d (lhs.get_app_fn.const_name,l) ) (rb_lmap.mk _ _) },
                 dependencies := [] },
  parser := lean.parser.ident }

meta def get_ext_projections (env : environment) (n : name) : tactic (list $ name × name) :=
do m ← projection_attr.get_cache,
   pure $ m.find n

meta def apply_congr : list expr → expr → tactic expr
| [] p := pure p
| (v :: vs) p :=
  mk_congr_fun p v >>= apply_congr vs

declare_trace simps_lemmas_names

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`. -/
@[replaceable]
meta def simps_add_projections' : ∀(e : environment) (nm : name) (suffix : string)
  (type lhs rhs : expr) (pr : option expr) (args : list expr) (univs : list name)
  (add_simp must_be_str short_nm : bool) (todo : list string), tactic unit
| e nm suffix type lhs rhs pr args univs add_simp must_be_str short_nm todo := do
  (type_args, tgt) ← mk_local_pis_whnf type,
  tgt ← whnf tgt,
  let new_args := args ++ type_args,
  let lhs_ap := lhs.mk_app type_args,
  let rhs_ap := rhs.instantiate_lambdas_or_apps type_args,
  pr ← traverse (apply_congr type_args) pr,
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
      eta ← expr.is_eta_expansion_aux rhs_ap pairs, -- check whether `rhs_ap` is an eta-expansion
      let rhs_ap := eta.lhoare rhs_ap, -- eta-reduce `rhs_ap`
      /- we want to generate the current projection if it is in `todo` or when `rhs_ap` was an
      eta-expansion -/
      when ("" ∈ todo ∨ (todo = [] ∧ eta.is_some)) $ do
        { simps_add_projection' (nm.append_suffix suffix) tgt lhs_ap rhs_ap pr new_args univs add_simp },
      -- if `rhs_ap` was an eta-expansion and `todo` is empty, we stop
      when ¬(todo = [""] ∨ (eta.is_some ∧ todo = [])) $ do
        /- remove "" from todo. This allows a to generate lemmas + nested version of them.
          This is not very useful, but this does improve error messages. -/
        let todo := todo.filter $ (≠ ""),
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).is_prefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).is_prefix_of x).iget,
            simp_lemma := nm.append_suffix $ suffix ++ x, needed_proj := (x.split_on '_').tail.head in
          fail format!"Invalid simp-lemma {simp_lemma}. Projection {needed_proj} doesn't exist.",
        pairs.mmap' $ λ ⟨proj, new_rhs⟩,
        do { new_type ← infer_type new_rhs,
             let new_todo := todo.filter_map $ λ x, string.drop_prefix x $ "_" ++ proj.last,
             b ← is_prop new_type,
             -- we only continue with this field if it is non-propositional or mentioned in todo
             when ((¬ b ∧ todo = []) ∨ (todo ≠ [] ∧ new_todo ≠ [])) $ do
               -- cannot use `mk_app` here, since the resulting application might still be a function.
               new_lhs ← mk_mapp proj $ (params ++ [lhs_ap]).map some,
               let new_suffix := if short_nm then "_" ++ proj.last else
                 suffix ++ "_" ++ proj.last,
               simps_add_projections' e nm new_suffix new_type new_lhs new_rhs none new_args univs
                 add_simp ff short_nm new_todo },
        let t_params := tgt.get_app_args,
        projs' ← get_ext_projections e str,
        projs'.mmap' $ λ ⟨proj,lmm⟩, try $
        do { d ← get_decl lmm,
             lmm ← mk_const lmm,
             new_lhs ← mk_mapp proj $ t_params.map some,
             (new_rhs, prf, _) ← rewrite lmm (new_lhs rhs_ap) { md := transparency.all },
             new_rhs ← instantiate_mvars new_rhs,
             prf ← instantiate_mvars prf,
             let new_lhs := new_lhs lhs_ap,
             new_type ← infer_type new_lhs,
             let new_todo := todo.filter_map $ λ x, string.drop_prefix x $ "_" ++ proj.last,
             let new_suffix := if short_nm then "_" ++ proj.last else
               suffix ++ "_" ++ proj.last,
             simps_add_projections' e nm new_suffix new_type new_lhs new_rhs (some prf) new_args univs
               add_simp ff short_nm new_todo }
    else do
      when must_be_str $
        fail "Invalid `simps` attribute. Body is not a constructor application",
      when (todo ≠ [] ∧ todo ≠ [""]) $
        fail format!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo.head}. Too many projections given.",
      simps_add_projection' (nm.append_suffix suffix) tgt lhs_ap rhs_ap pr new_args univs add_simp
  else do
    when must_be_str $
      fail "Invalid `simps` attribute. Target is not a structure",
    when (todo ≠ [] ∧ todo ≠ [""]) $
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo.head}. Too many projections given.",
    simps_add_projection' (nm.append_suffix suffix) tgt lhs_ap rhs_ap pr new_args univs add_simp

/-- `simps_tac` derives simp-lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name.
  -/
meta def simps_tac (nm : name) (add_simp : bool) (short_nm : bool := ff)
  (todo : list string := []) : tactic unit := do
  e ← get_env,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  let todo := todo.erase_dup.map $ λ proj, "_" ++ proj,
  let t := d.type,
  pr ← mk_app ``rfl [t,lhs],
  simps_add_projections e nm "" d.type lhs d.value pr [] d.univ_params add_simp tt short_nm todo

reserve notation `lemmas_only`
reserve notation `short_name`
setup_tactic_parser

/-- The parser for simps. Pattern: `'lemmas_only'? ident*` -/
meta def simps_parser : parser (bool × bool × list string) :=
/- note: we currently don't check whether the user has written a nonsense namespace as arguments. -/
prod.mk <$> (option.is_none <$> (tk "lemmas_only")?) <*>
(prod.mk <$> (option.is_some <$> (tk "short_name")?) <*> many (name.last <$> ident))


/--
* Automatically derive lemmas specifying the projections of this declaration.
* Example: (note that the forward and reverse functions are specified differently!)
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
* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections. For example:
  ```
  attribute [simps to_fun] refl
  ```
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

Using `set_option trace.simps_lemmas_names true` before the attribute `@[simps]` will list
the lemmas being declared.
  -/
@[user_attribute] meta def simps_attr : user_attribute unit (bool × bool × list string) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simps_parser,
  after_set := some $
    λ n _ _, do (add_simp, short_nm, todo) ← simps_attr.get_param n,
      simps_tac n add_simp short_nm todo }

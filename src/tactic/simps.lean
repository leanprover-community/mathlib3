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
reserve notation `initialize_simps_projections`
declare_trace simps.verbose

/--
The `@[_simps_str]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- This will usually be tagged by the `@[simps]` tactic.
- You can also generate this with the command `initialize_simps_projections`.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is the expressions that correspond to the projections of the structure
  (these can contain the universe parameters specified in the first argument).
-/
@[user_attribute] meta def simps_str_attr : user_attribute unit (list name × list expr) :=
{ name := `_simps_str,
  descr := "An attribute specifying the projection of the given structure.",
  parser := do e ← texpr, eval_pexpr _ e }

/--
  The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `tt` for notation classes and `ff` for classes applied to the structure,
    like `has_coe_to_sort` and `has_coe_to_fun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
@[user_attribute] meta def notation_class_attr : user_attribute unit (bool × option name) :=
{ name := `notation_class,
  descr := "An attribute specifying that this is a notation class. Used by @[simps].",
  parser := prod.mk <$> (option.is_none <$> (tk "*")?) <*> ident? }

attribute [notation_class] has_zero has_one has_add has_mul has_inv has_neg has_sub has_div has_dvd
  has_mod has_le has_lt has_append has_andthen has_union has_inter has_sdiff has_equiv has_subset
  has_ssubset has_emptyc has_insert has_singleton has_sep has_mem has_pow

attribute [notation_class* coe_sort] has_coe_to_sort
attribute [notation_class* coe_fn] has_coe_to_fun

/--
  Finds an instance of an implication `cond → tgt`.
  Returns a pair of a local constant `e` of type `cond`, and an instance of `tgt` that can mention `e`.
-/
meta def mk_conditional_instance (cond tgt : expr) : tactic (expr × expr) := do
f ← mk_meta_var cond,
e ← assertv `c cond f, swap,
reset_instance_cache,
inst ← mk_instance tgt,
return (e, inst)

/--
  Get the projections used by `simps` associated to a given structure `str`. The second component is
  the list of projections, and the first component the (shared) list of universe levels used by the
  projections.
  The returned universe levels are the universe levels of the structure. For the projections there
  are three cases
  * If the declaration `{structure_name}.simps.{projection_name}` has been declared, then the value
    of this declaration is used (after checking that it is definitionally equal to the actual
    projection
  * Otherwise, for every class with the `notation_class` attribute, and the structure has an
    instance of that notation class, then the projection of that notation class is used for the
    projection that is definitionally equal to it (if there is such a projection).
    This means in practice that coercions to function types and sorts will be used instead of
    a projection, if this coercion is definitionally equal to a projection. Furthermore, for
    notation classes like `has_mul` and `has_zero` those projections are used instead of the
    corresponding projection
  * Otherwise, the projection of the structure is chosen.
    For example: ``simps_get_raw_projections env `prod`` gives the default projections
    ```
      ([u, v], [prod.fst.{u v}, prod.snd.{u v}])
    ```
    while ``simps_get_raw_projections env `equiv`` gives
    ```
      ([u_1, u_2], [λ α β, coe_fn, λ {α β} (e : α ≃ β), ⇑(e.symm), left_inv, right_inv])
    ```
    after declaring the coercion from `equiv` to function and adding the declaration
    ```
      def equiv.simps.inv_fun {α β} (e : α ≃ β) : β → α := e.symm
    ```
-/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
meta def simps_get_raw_projections (e : environment) (str : name) :
  tactic (list name × list expr) := do
  has_attr ← has_attribute' `_simps_str str,
  if has_attr then do
    when_tracing `simps.verbose trace!"[simps] > found projection information for structure {str}",
    simps_str_attr.get_param str
  else do
    when_tracing `simps.verbose trace!"[simps] > generating projection information for structure {str}:",
    d_str ← e.get str,
    projs ← e.structure_fields_full str,
    let raw_univs := d_str.univ_params,
    let raw_levels := level.param <$> raw_univs,
    /- Define the raw expressions for the projections, by default as the projections
    (as an expression), but this can be overriden by the user. -/
    raw_exprs ← projs.mmap (λ proj, let raw_expr : expr := expr.const proj raw_levels in do
      custom_proj ← (do
        decl ← e.get (str ++ `simps ++ proj.last),
        let custom_proj := decl.value.instantiate_univ_params $ decl.univ_params.zip raw_levels,
        when_tracing `simps.verbose trace!"[simps] > found custom projection for {proj}:\n        > {custom_proj}",
        return custom_proj) <|> return raw_expr,
      is_def_eq custom_proj raw_expr <|>
        fail!"Invalid custom projection:\n {custom_proj}\nExpression is not definitionally equal to {raw_expr}.",
      return custom_proj),
    /- check for other coercions and type-class arguments to use as projections instead. -/
    (args, _) ← mk_local_pis d_str.type,
    let e_str := (expr.const str raw_levels).mk_app args,
    automatic_projs ← attribute.get_instances `notation_class,
    raw_exprs ← automatic_projs.mfoldl (λ (raw_exprs : list expr) class_nm, (do
      (is_class, proj_nm) ← notation_class_attr.get_param class_nm,
      proj_nm ← proj_nm <|> (e.structure_fields_full class_nm).map list.head,
      (raw_expr, lambda_raw_expr) ← if is_class then (do
        guard $ args.length = 1,
        let e_inst_type := (expr.const class_nm raw_levels).mk_app args,
        (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type),
        raw_expr ← mk_mapp proj_nm [args.head, e_inst],
        raw_expr_lambda ← lambdas [hyp] raw_expr, -- expr.bind_lambda doesn't give the correct type
        return (raw_expr, raw_expr_lambda.lambdas args))
      else (do
        e_inst_type ← to_expr ((expr.const class_nm []).app (pexpr.of_expr e_str)),
        e_inst ← try_for 1000 (mk_instance e_inst_type),
        raw_expr ← mk_mapp proj_nm [e_str, e_inst],
        return (raw_expr, raw_expr.lambdas args)),
      raw_expr_whnf ← whnf raw_expr.binding_body,
      let relevant_proj := raw_expr_whnf.get_app_fn.const_name,
      /- use this as projection, if the function reduces to a projection, and this projection has
        not been overrriden by the user. -/
      guard (projs.any (= relevant_proj) ∧ ¬ e.contains (str ++ `simps ++ relevant_proj.last)),
      let pos := projs.find_index (= relevant_proj),
      when_tracing `simps.verbose trace!"        > using function {proj_nm} instead of the default projection {relevant_proj.last}.",
      return $ raw_exprs.update_nth pos lambda_raw_expr) <|> return raw_exprs) raw_exprs,
    when_tracing `simps.verbose trace!"[simps] > generated projections for {str}:\n        > {raw_exprs}",
    simps_str_attr.set str (raw_univs, raw_exprs) tt,
    return (raw_univs, raw_exprs)

/--
  You can specify custom projections for the `@[simps]` attribute.
  To do this for the projection `my_structure.awesome_projection` by adding a declaration
  `my_structure.simps.awesome_projection` that is definitionally equal to
  `my_structure.awesome_projection` but has the projection in the desired (simp-normal) form.

  You can initialize the projections `@[simps]` uses with `initialize_simps_projections`
  (after declaring any custom projections). This is not necessary, it has the same effect
  if you just add `@[simps]` to a declaration.

  If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initialize_simps_projections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.
-/
library_note "custom simps projection"

/-- Specify simps projections, see Note [custom simps projection].
  Set `trace.simps.verbose` to true to see the generated projections. -/
@[user_command] meta def initialize_simps_projections_cmd
  (_ : parse $ tk "initialize_simps_projections") : parser unit := do
  env ← get_env,
  ns ← many ident,
  ns.mmap' $ λ nm, do nm ← resolve_constant nm, simps_get_raw_projections env nm

/--
  Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of triples (projection expression, projection name, corresponding right-hand-side),
  one for each projection.

  Example: ``simps_get_projection_exprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(@prod.fst.{u v} α β), `prod.fst, `(x)), (`(@prod.snd.{u v} α β), `prod.snd, `(y))]
  ```
-/
-- This function does not use `tactic.mk_app` or `tactic.mk_mapp`, because the the given arguments
-- might not uniquely specify the universe levels yet.
meta def simps_get_projection_exprs (e : environment) (tgt : expr)
  (rhs : expr) : tactic $ list $ expr × name × expr := do
  let params := get_app_args tgt, -- the parameters of the structure
  guard ((get_app_args rhs).take params.length = params) <|> fail "unreachable code (1)",
  let str := tgt.get_app_fn.const_name,
  projs ← e.structure_fields_full str,
  let rhs_args := (get_app_args rhs).drop params.length, -- the fields of the object
  guard (rhs_args.length = projs.length) <|> fail "unreachable code (2)",
  (raw_univs, raw_exprs) ← simps_get_raw_projections e str,
  let univs := raw_univs.zip tgt.get_app_fn.univ_levels,
  let proj_exprs := raw_exprs.map $
    λ raw_expr, (raw_expr.instantiate_univ_params univs).instantiate_lambdas_or_apps params,
  return $ proj_exprs.zip $ projs.zip rhs_args

/--
  Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    The attributes can be either basic attributes, or user attributes without parameters.
  * `short_name` gives the generated lemmas a shorter name
  * if `simp_rhs` is `tt` then the right-hand-side of the generated lemmas will be put simp-normal form
  * `type_md` specifies how aggressively definitions are unfolded in the type of expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `rhs_md` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `none`
  * If `fully_applied` is `ff` then the generated simp-lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
-/
@[derive [has_reflect, inhabited]] structure simps_cfg :=
(attrs         := [`simp])
(short_name    := ff)
(simp_rhs      := ff)
(type_md       := transparency.instances)
(rhs_md        := transparency.none)
(fully_applied := tt)

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables.
  If `add_simp` then we make the resulting lemma a simp-lemma. -/
meta def simps_add_projection (nm : name) (type lhs rhs : expr) (args : list expr)
  (univs : list name) (cfg : simps_cfg) : tactic unit := do
  -- simplify `rhs` if `simp_rhs` and `simp` makes progress
  (rhs, prf) ← (guard cfg.simp_rhs >> rhs.simp) <|> prod.mk rhs <$> mk_app `eq.refl [type, lhs],
  eq_ap ← mk_mapp `eq $ [type, lhs, rhs].map some,
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := prf.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  when_tracing `simps.verbose trace!"[simps] > adding projection\n        > {decl_name} : {decl_type}",
  decorate_error ("failed to add projection lemma " ++ decl_name.to_string ++ ". Nested error:") $
    add_decl decl,
  b ← succeeds $ is_def_eq lhs rhs,
  when (b ∧ `simp ∈ cfg.attrs) (set_basic_attribute `_refl_lemma decl_name tt),
  cfg.attrs.mmap' $ λ nm, set_attribute nm decl_name tt

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`. -/
meta def simps_add_projections : ∀(e : environment) (nm : name) (suffix : string)
  (type lhs rhs : expr) (args : list expr) (univs : list name) (must_be_str : bool)
  (cfg : simps_cfg) (todo : list string), tactic unit
| e nm suffix type lhs rhs args univs must_be_str cfg todo := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  (type_args, tgt) ← mk_local_pis_whnf type cfg.type_md,
  tgt ← whnf tgt,
  let new_args := args ++ type_args,
  let lhs_ap := lhs.mk_app type_args,
  let rhs_ap := rhs.instantiate_lambdas_or_apps type_args,
  let str := tgt.get_app_fn.const_name,
  let new_nm := nm.append_suffix suffix,
  /- We want to generate the current projection if it is in `todo` -/
  let todo_next := todo.filter (≠ ""),
  /- Don't recursively continue if `str` is not a structure. As a special case, also don't
    recursively continue if the nested structure is `prod` or `pprod`, unless projections are
    specified manually. -/
  if e.is_structure str ∧ ¬(todo = [] ∧ str ∈ [`prod, `pprod] ∧ ¬must_be_str) then do
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    rhs_whnf ← whnf rhs_ap cfg.rhs_md,
    (rhs_ap, todo_now) ← if h : ¬is_constant_of rhs_ap.get_app_fn intro ∧
      is_constant_of rhs_whnf.get_app_fn intro then
      /- If this was a desired projection, we want to apply it before taking the whnf.
        However, if the current field is an eta-expansion (see below), we first want
        to eta-reduce it and only then construct the projection.
        This makes the flow of this function hard to follow. -/
      when ("" ∈ todo) (if cfg.fully_applied then
        simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
        simps_add_projection new_nm type lhs rhs args univs cfg) >>
      return (rhs_whnf, ff) else
      return (rhs_ap, "" ∈ todo),
    if is_constant_of (get_app_fn rhs_ap) intro then do -- if the value is a constructor application
      tuples ← simps_get_projection_exprs e tgt rhs_ap,
      let projs := tuples.map $ λ x, x.2.1,
      let pairs := tuples.map $ λ x, x.2,
      eta ← expr.is_eta_expansion_aux rhs_ap pairs, -- check whether `rhs_ap` is an eta-expansion
      let rhs_ap := eta.lhoare rhs_ap, -- eta-reduce `rhs_ap`
      /- As a special case, we want to automatically generate the current projection if `rhs_ap`
        was an eta-expansion. Also, when this was a desired projection, we need to generate the
        current projection if we haven't done it above. -/
      when (todo_now ∨ (todo = [] ∧ eta.is_some)) $
        if cfg.fully_applied then
          simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
          simps_add_projection new_nm type lhs rhs args univs cfg,
      /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
      automatically choose projections -/
      when ¬(todo = [""] ∨ (eta.is_some ∧ todo = [])) $ do
        let todo := todo_next,
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).is_prefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).is_prefix_of x).iget,
            simp_lemma := nm.append_suffix $ suffix ++ x,
            needed_proj := (x.split_on '_').tail.head in
          fail!"Invalid simp-lemma {simp_lemma}. Projection {needed_proj} doesn't exist.",
        tuples.mmap' $ λ ⟨proj_expr, proj, new_rhs⟩, do
          new_type ← infer_type new_rhs,
          let new_todo := todo.filter_map $ λ x, string.get_rest x $ "_" ++ proj.last,
          b ← is_prop new_type,
          -- we only continue with this field if it is non-propositional or mentioned in todo
          when ((¬ b ∧ todo = []) ∨ new_todo ≠ []) $ do
            let new_lhs := proj_expr.instantiate_lambdas_or_apps [lhs_ap],
            let new_suffix := if cfg.short_name then "_" ++ proj.last else
              suffix ++ "_" ++ proj.last,
            simps_add_projections e nm new_suffix new_type new_lhs new_rhs new_args univs
              ff cfg new_todo
    else do
      when must_be_str $
        fail!"Invalid `simps` attribute. The body is not a constructor application:\n{rhs_ap}\nPossible solution: add option {{rhs_md := semireducible}.",
      when (todo_next ≠ []) $
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo_next.head}. The given definition is not a constructor application:\n{rhs_ap}\nPossible solution: add option {{rhs_md := semireducible}.",
      if cfg.fully_applied then
        simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
        simps_add_projection new_nm type lhs rhs args univs cfg
  else do
    when must_be_str $
      fail "Invalid `simps` attribute. Target is not a structure",
    when (todo_next ≠ [] ∧ str ∉ [`prod, `pprod]) $
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo_next.head}. Projection {(todo_next.head.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    if cfg.fully_applied then
      simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
      simps_add_projection new_nm type lhs rhs args univs cfg

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
  (do some e ← parser.pexpr? | return {}, eval_pexpr simps_cfg e)

/--
The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two simp-lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive simp-lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `has_mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{structure_name}.simps.{projection_name}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.inv_fun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_to_fun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_inv_fun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
  * Exception: by default it will not recursively create simp-lemmas for fields in the structures
    `prod` and `pprod`. Give explicit projection names to override this.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma  foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure equiv_plus_data (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : equiv_plus_data α α := { data := tt, ..equiv.refl α }
  ```
  generates the following, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`:
  ```lean
  @[simp] lemma bar_to_equiv : ∀ {α : Sort u_1}, bar.to_equiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort u_1}, bar.data = tt
  ```
* For configuration options, see the doc string of `simps_cfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an expression of type `simps_cfg`.
* If one of the projections is marked as a coercion, the generated lemmas do *not* use this
  coercion.
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates.
  -/

@[user_attribute] meta def simps_attr : user_attribute unit (list string × simps_cfg) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simps_parser,
  after_set := some $
    λ n _ _, do (todo, cfg) ← simps_attr.get_param n, simps_tac n cfg todo }

open function
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

local infix ` ≃ `:25 := equiv

@[simps] protected def equiv.refl (α) : α ≃ α :=
⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

set_option trace.simps.verbose true
structure equiv_plus_data (α β) extends α ≃ β := (data : bool)
/-
[simps] > generating projection information for structure equiv_plus_data:
[simps] > generated projections for equiv_plus_data:
        > [equiv_plus_data.to_equiv, equiv_plus_data.data]
[simps] > found projection information for structure equiv
[simps] > adding projection
        > bar_to_equiv : ∀ {α : Sort u_1}, bar.to_equiv = equiv.refl α
[simps] > adding projection
        > bar_data : ∀ {α : Sort u_1}, bar.data = tt

-/

@[simps] def bar {α} : equiv_plus_data α α := { data := tt, ..equiv.refl α }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  decl_names               := [`simps_attr],
  tags                     := ["simplification"] }

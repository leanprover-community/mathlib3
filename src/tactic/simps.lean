/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core
import data.sum

/-!
# simps attribute

This file defines the `@[simps]` attribute, to automatically generate simp-lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `simps_attr` and `simps_cfg` for more details and
  configuration options.
* `@[_simps_str]` is automatically added to structures that have been used in `@[simps]` at least
  once. This attribute contains the data of the projections used for this structure by all following
  invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `has_mul` and
  `has_zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `has_mul` is tagged with `@[notation_class]` then the projection used for `semigroup`
  will be `λ α hα, @has_mul.mul α (@semigroup.to_has_mul α hα)` instead of `@semigroup.mul`.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

open tactic expr option sum

setup_tactic_parser
declare_trace simps.verbose
declare_trace simps.debug

/--
The `@[_simps_str]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- This will usually be tagged by the `@[simps]` tactic.
- You can also generate this with the command `initialize_simps_projections`.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is a list that consists of
  - a custom name for each projection of the structure
  - an expressions for each projections of the structure (definitionally equal to the
    corresponding projection). These expressions can contain the universe parameters specified
    in the first argument).
  - a list of natural numbers, which is the projection number(s) that have to be applied to the
    expression. For example the list `[0, 1]` corresponds to applying the first projection of the
    structure, and then the second projection of the resulting structure (this assumes that the
    target of the first projection is a structure with at least two projections).
    The composition of these projections is required to be definitionally equal to the provided
    expression.
  - A boolean specifying whether simp-lemmas are generated for this projection by default.
-/
@[user_attribute] meta def simps_str_attr :
  user_attribute unit (list name × list (name × expr × list ℕ × bool)) :=
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

/-- Returns the projection information of a structure. -/
meta def projections_info (l : list (name × expr × list ℕ × bool)) (pref : string) (str : name) :
  tactic format := do
  ⟨defaults, nondefaults⟩ ← return $ l.partition_map $
    λ s, if s.2.2.2 then inl s else inr s,
  to_print ← defaults.mmap $ λ s, to_string <$> pformat!"Projection {s.1}: {s.2.1}",
  let print2 := string.join $ (nondefaults.map (λ nm : _ × _, to_string nm.1)).intersperse ", ",
  let to_print := to_print ++ if nondefaults = [] then [] else
    ["No lemmas are generated for the projections: " ++ print2 ++ "."],
  let to_print := string.join $ to_print.intersperse "\n        > ",
  return format!"[simps] > {pref} {str}:\n        > {to_print}"

/-- Auxilliary function of `get_composite_of_projections`. -/
meta def get_composite_of_projections_aux : Π (str : name) (proj : string) (x : expr)
  (pos : list ℕ) (args : list expr), tactic (expr × list ℕ) | str proj x pos args := do
  e ← get_env,
  projs ← e.structure_fields str,
  let proj_info := projs.map_with_index $ λ n p, (λ x, (x, n, p)) <$> proj.get_rest ("_" ++ p.last),
  when (proj_info.filter_map id = []) $
    fail!"Failed to find constructor {proj.popn 1} in structure {str}.",
  (proj_rest, index, proj_nm) ← return (proj_info.filter_map id).ilast,
  str_d ← e.get str,
  let proj_e : expr := const (str ++ proj_nm) str_d.univ_levels,
  proj_d ← e.get (str ++ proj_nm),
  type ← infer_type x,
  let params := get_app_args type,
  let univs := proj_d.univ_params.zip type.get_app_fn.univ_levels,
  let new_x := (proj_e.instantiate_univ_params univs).mk_app $ params ++ [x],
  let new_pos := pos ++ [index],
  if proj_rest.is_empty then return (new_x.lambdas args, new_pos) else do
    type ← infer_type new_x,
    (type_args, tgt) ← open_pis_whnf type,
    let new_str := tgt.get_app_fn.const_name,
    get_composite_of_projections_aux new_str proj_rest (new_x.mk_app type_args) new_pos
      (args ++ type_args)

/-- Given a structure `str` and a projection `proj`, that could be multiple nested projections
  (separated by `_`), returns an expression that is the composition of these projections and a
  list of natural numbers, that are the projection numbers of the applied projections. -/
meta def get_composite_of_projections (str : name) (proj : string) : tactic (expr × list ℕ) := do
  e ← get_env,
  str_d ← e.get str,
  let str_e : expr := const str str_d.univ_levels,
  type ← infer_type str_e,
  (type_args, tgt) ← open_pis_whnf type,
  let str_ap := str_e.mk_app type_args,
  x ← mk_local' `x binder_info.default str_ap,
  get_composite_of_projections_aux str ("_" ++ proj) x [] $ type_args ++ [x]

/--
  Get the projections used by `simps` associated to a given structure `str`.

  The returned information is also stored in a parameter of the attribute `@[_simps_str]`, which
  is given to `str`. If `str` already has this attribute, the information is read from this
  attribute instead. See the documentation for this attribute for the data this tactic returns.

  The returned universe levels are the universe levels of the structure. For the projections there
  are three cases
  * If the declaration `{structure_name}.simps.{projection_name}` has been declared, then the value
    of this declaration is used (after checking that it is definitionally equal to the actual
    projection. If you rename the projection name, the declaration should have the *new* projection
    name.
  * You can also declare a custom projection that is a composite of multiple projections.
  * Otherwise, for every class with the `notation_class` attribute, and the structure has an
    instance of that notation class, then the projection of that notation class is used for the
    projection that is definitionally equal to it (if there is such a projection).
    This means in practice that coercions to function types and sorts will be used instead of
    a projection, if this coercion is definitionally equal to a projection. Furthermore, for
    notation classes like `has_mul` and `has_zero` those projections are used instead of the
    corresponding projection.
    Projections for coercions and notation classes are not automatically generated if they are
    composites of multiple projections (for example when you use `extend` without the
    `old_structure_cmd`).
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

  Optionally, this command accepts three optional arguments:
  * If `trace_if_exists` the command will always generate a trace message when the structure already
    has the attribute `@[_simps_str]`.
  * The `rules` argument accepts a list of pairs `sum.inl (old_name, new_name)`. This is used to
    change the projection name `old_name` to the custom projection name `new_name`. Example:
    for the structure `equiv` the projection `to_fun` could be renamed `apply`. This name will be
    used for parsing and generating projection names. This argument is ignored if the structure
    already has an existing attribute. If an element of `rules` is of the form `sum.inr name`, this
    means that the projection `name` will not be applied by default.
  * if `trc` is true, this tactic will trace information.
-/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
meta def simps_get_raw_projections (e : environment) (str : name) (trace_if_exists : bool := ff)
  (rules : list (name × name ⊕ name) := []) (trc := ff) :
  tactic (list name × list (name × expr × list ℕ × bool)) := do
  let trc := trc || is_trace_enabled_for `simps.verbose,
  has_attr ← has_attribute' `_simps_str str,
  if has_attr then do
    data ← simps_str_attr.get_param str,
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    when (trace_if_exists || is_trace_enabled_for `simps.verbose) $ projections_info data.2
      "Already found projection information for structure" str >>= trace,
    return data
  else do
    when trc trace!"[simps] > generating projection information for structure {str}.",
    when_tracing `simps.debug trace!"[simps] > Applying the rules {rules}.",
    d_str ← e.get str,
    let raw_univs := d_str.univ_params,
    let raw_levels := level.param <$> raw_univs,
    /- Figure out projections, including renamings. The information for a projection is (before we
    figure out the `expr` of the projection:
    `(original name, given name, is default)`.
    The first projections are always the actual projections of the structure, but `rules` could
    specify custom projections that are compositions of multiple projections. -/
    projs ← e.structure_fields str,
    let projs := projs.map_with_index (λ n nm, (nm, nm, tt)),
    let projs : list (name × name × bool) := rules.foldl (λ projs rule,
      match rule with
      | (inl (old_nm, new_nm)) := if old_nm ∈ projs.map (λ x, x.2.1) then
         projs.map $ λ proj,
          if proj.2.1 = old_nm then (proj.1, new_nm, proj.2.2) else proj else
        projs ++ [(old_nm, new_nm, tt)]
      | (inr nm) := if nm ∈ projs.map (λ x, x.2.1) then
        projs.map $ λ proj,
          if proj.2.1 = nm then (proj.1, proj.2.1, ff) else proj else
        projs ++ [(nm, nm, ff)]
      end) projs,
    when_tracing `simps.debug trace!"[simps] > Projection info after applying the rules: {projs}.",
    when ¬ (projs.map (λ x : name × name × bool, x.2.1)).nodup $
      fail $ "Invalid projection names. Two projections have the same name.
This is likely because a custom composition of projections was given the same name as an " ++ "existing projection. Solution: rename the existing projection (before renaming the custom " ++ "projection).",
    /- Define the raw expressions for the projections, by default as the projections
    (as an expression), but this can be overriden by the user. -/
    raw_exprs_and_nrs ← projs.mmap $ λ ⟨orig_nm, new_nm, _⟩, do {
      (raw_expr, nrs) ← get_composite_of_projections str orig_nm.last,
      custom_proj ← do {
        decl ← e.get (str ++ `simps ++ new_nm.last),
        let custom_proj := decl.value.instantiate_univ_params $ decl.univ_params.zip raw_levels,
        when trc trace!
          "[simps] > found custom projection for {new_nm}:\n        > {custom_proj}",
        return custom_proj } <|> return raw_expr,
      is_def_eq custom_proj raw_expr <|>
        -- if the type of the expression is different, we show a different error message, because
        -- that is more likely going to be helpful.
        do {
          custom_proj_type ← infer_type custom_proj,
          raw_expr_type ← infer_type raw_expr,
          b ← succeeds (is_def_eq custom_proj_type raw_expr_type),
          if b then fail!"Invalid custom projection:\n  {custom_proj}
Expression is not definitionally equal to\n  {raw_expr}"
          else fail!"Invalid custom projection:\n  {custom_proj}
Expression has different type than {str ++ orig_nm}. Given type:\n  {custom_proj_type}
Expected type:\n  {raw_expr_type}" },
      return (custom_proj, nrs) },
    let raw_exprs := raw_exprs_and_nrs.map prod.fst,
    /- Check for other coercions and type-class arguments to use as projections instead. -/
    (args, _) ← open_pis d_str.type,
    let e_str := (expr.const str raw_levels).mk_app args,
    automatic_projs ← attribute.get_instances `notation_class,
    raw_exprs ← automatic_projs.mfoldl (λ (raw_exprs : list expr) class_nm, do {
      (is_class, proj_nm) ← notation_class_attr.get_param class_nm,
      proj_nm ← proj_nm <|> (e.structure_fields_full class_nm).map list.head,
      /- For this class, find the projection. `raw_expr` is the projection found applied to `args`,
        and `lambda_raw_expr` has the arguments `args` abstracted. -/
      (raw_expr, lambda_raw_expr) ← if is_class then (do
        guard $ args.length = 1,
        let e_inst_type := (const class_nm raw_levels).mk_app args,
        (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type),
        raw_expr ← mk_mapp proj_nm [args.head, e_inst],
        clear hyp,
        -- Note: `expr.bind_lambda` doesn't give the correct type
        raw_expr_lambda ← lambdas [hyp] raw_expr,
        return (raw_expr, raw_expr_lambda.lambdas args))
      else (do
        e_inst_type ← to_expr ((const class_nm []).app (pexpr.of_expr e_str)),
        e_inst ← try_for 1000 (mk_instance e_inst_type),
        raw_expr ← mk_mapp proj_nm [e_str, e_inst],
        return (raw_expr, raw_expr.lambdas args)),
      raw_expr_whnf ← whnf raw_expr,
      let relevant_proj := raw_expr_whnf.binding_body.get_app_fn.const_name,
      /- Use this as projection, if the function reduces to a projection, and this projection has
        not been overrriden by the user. -/
      guard $ projs.any $
        λ x, x.1 = relevant_proj.last ∧ ¬ e.contains (str ++ `simps ++ x.2.1.last),
      let pos := projs.find_index (λ x, x.1 = relevant_proj.last),
      when trc trace!
        "        > using {proj_nm} instead of the default projection {relevant_proj.last}.",
      when_tracing `simps.debug trace!"[simps] > The raw projection is:\n  {lambda_raw_expr}",
      return $ raw_exprs.update_nth pos lambda_raw_expr } <|> return raw_exprs) raw_exprs,
    let positions := raw_exprs_and_nrs.map prod.snd,
    let defaults := projs.map (λ x, x.2.2),
    let proj_names := projs.map (λ x, x.2.1),
    let projs := proj_names.zip $ raw_exprs.zip $ positions.zip defaults,
    /- make all proof non-default. -/
    projs ← projs.mmap $ λ proj,
      is_proof proj.2.1 >>= λ b, return $ if b then (proj.1, proj.2.1, proj.2.2.1, ff) else proj,
    when trc $ projections_info projs "generated projections for" str >>= trace,
    simps_str_attr.set str (raw_univs, projs) tt,
    when_tracing `simps.debug trace!
      "[simps] > Generated raw projection data: \n{(raw_univs, projs)}",
    return (raw_univs, projs)

/-- Parse a rule for `initialize_simps_projections`. It is either `<name>→<name>` or `-<name>`.-/
meta def simps_parse_rule : parser (name × name ⊕ name) :=
(λ x y, inl (x, y)) <$> ident <*> (tk "->" >> ident) <|> inr <$> (tk "-" >> ident)

/--
  You can specify custom projections for the `@[simps]` attribute.
  To do this for the projection `my_structure.original_projection` by adding a declaration
  `my_structure.simps.my_projection` that is definitionally equal to
  `my_structure.original_projection` but has the projection in the desired (simp-normal) form.
  Then you can call
  ```
  initialize_simps_projections (original_projection → my_projection, ...)
  ```
  to register this projection.

  Running `initialize_simps_projections` without arguments is not necessary, it has the same effect
  if you just add `@[simps]` to a declaration.

  If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initialize_simps_projections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.
-/
library_note "custom simps projection"

/-- Specify simps projections, see Note [custom simps projection].
  * You can specify custom names by writing e.g.
    `initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)`.
  * You can disable a projection by default by running
    `initialize_simps_projections equiv (-inv_fun)`
    This will ensure that no simp lemmas are generated for this projection,
    unless this projection is explicitly specified by the user.
  * Run `initialize_simps_projections?` (or set `trace.simps.verbose`)
    to see the generated projections. -/
@[user_command] meta def initialize_simps_projections_cmd
  (_ : parse $ tk "initialize_simps_projections") : parser unit := do
  env ← get_env,
  trc ← is_some <$> (tk "?")?,
  ns ← (prod.mk <$> ident <*> (tk "(" >> sep_by (tk ",") simps_parse_rule <* tk ")")?)*,
  ns.mmap' $ λ data, do
    nm ← resolve_constant data.1,
    simps_get_raw_projections env nm tt (data.2.get_or_else []) trc

/--
  Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    The attributes can be either basic attributes, or user attributes without parameters.
    There are two attributes which `simps` might add itself:
    * If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    * If the definition is marked with `@[to_additive ...]` then all generated lemmas are marked
      with `@[to_additive]`
  * `short_name` gives the generated lemmas a shorter name. This only has an effect when multiple
    projections are applied in a lemma. When this is `ff` (default) all projection names will be
    appended to the definition name to form the lemma name, and when this is `tt`, only the
    last projection name will be appended.
  * if `simp_rhs` is `tt` then the right-hand-side of the generated lemmas will be put in
    simp-normal form. More precisely: `dsimp, simp` will be called on all these expressions.
    See note [dsimp, simp].
  * `type_md` specifies how aggressively definitions are unfolded in the type of expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `rhs_md` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `none`
    Exception: `@[simps]` will automatically add the options
    `{rhs_md := semireducible, simp_rhs := tt}` if the given definition is not a constructor with
    the given reducibility setting for `rhs_md`.
  * If `fully_applied` is `ff` then the generated simp-lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
  * The option `not_recursive` contains the list of names of types for which `@[simps]` doesn't
    recursively apply projections. For example, given an equivalence `α × β ≃ β × α` one usually
    wants to only apply the projections for `equiv`, and not also those for `×`. This option is
    only relevant if no explicit projection names are given as argument to `@[simps]`.
  * The option `trace` is set to `tt` when you write `@[simps?]`. In this case, the attribute will
    print all generated lemmas. It is almost the same as setting the option `trace.simps.verbose`,
    except that it doesn't print information about the found projections.
-/
@[derive [has_reflect, inhabited]] structure simps_cfg :=
(attrs         := [`simp])
(short_name    := ff)
(simp_rhs      := ff)
(type_md       := transparency.instances)
(rhs_md        := transparency.none)
(fully_applied := tt)
(not_recursive := [`prod, `pprod])
(trace         := ff)

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied expressions. -/
def as_fn : simps_cfg := {fully_applied := ff}
/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def lemmas_only : simps_cfg := {attrs := []}

/--
  Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of quintuples
  ```
  (projection expression, given projection name, corresponding right-hand-side, projection numbers,
    used by default)
  ```
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simps_get_projection_exprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(@prod.fst.{u v} α β), `fst, `(x), [0], tt),
     (`(@prod.snd.{u v} α β), `snd, `(y), [1], tt)]
  ```

  Example 2: ``simps_get_projection_exprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(@equiv.to_fun.{u u} α α), `apply, `(id), [0], tt),
     (`(@equiv.inv_fun.{u u} α α), `symm_apply, `(id), [1], tt),
     ...,
     ...]
  ```
  The last two fields of the list correspond to the propositional fields of the structure,
  and are rarely/never used.
-/
-- This function does not use `tactic.mk_app` or `tactic.mk_mapp`, because the given arguments
-- might not uniquely specify the universe levels yet.
meta def simps_get_projection_exprs (e : environment) (tgt : expr)
  (rhs : expr) (cfg : simps_cfg) : tactic $ list $ expr × name × expr × list ℕ × bool := do
  let params := get_app_args tgt, -- the parameters of the structure
  (params.zip $ (get_app_args rhs).take params.length).mmap' (λ ⟨a, b⟩, is_def_eq a b)
    <|> fail "unreachable code (1)",
  let str := tgt.get_app_fn.const_name,
  let rhs_args := (get_app_args rhs).drop params.length, -- the fields of the object
  (raw_univs, proj_data) ← simps_get_raw_projections e str ff [] cfg.trace,
  let univs := raw_univs.zip tgt.get_app_fn.univ_levels,
  let projs := proj_data.map prod.fst,
  let raw_exprs := proj_data.map $ λ p, p.2.1,
  let nrs_and_default := proj_data.map $ λ p, p.2.2,
  let proj_exprs := raw_exprs.map $
    λ raw_expr, (raw_expr.instantiate_univ_params univs).instantiate_lambdas_or_apps params,
  let rhs_exprs := nrs_and_default.map $ λ x, rhs_args.inth x.1.head,
  return $ proj_exprs.zip $ projs.zip $ rhs_exprs.zip $ nrs_and_default.map (λ x, (x.1.tail, x.2))

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables.
  If `add_simp` then we make the resulting lemma a simp-lemma. -/
meta def simps_add_projection (nm : name) (type lhs rhs : expr) (args : list expr)
  (univs : list name) (cfg : simps_cfg) : tactic unit := do
  when_tracing `simps.debug trace!
    "[simps] > Planning to add the equality\n        > {lhs} = ({rhs} : {type})",
  -- simplify `rhs` if `cfg.simp_rhs` is true
  (rhs, prf) ← do { guard cfg.simp_rhs,
    rhs' ← rhs.dsimp {fail_if_unchanged := ff},
    when_tracing `simps.debug $ when (rhs ≠ rhs') trace!
      "[simps] > `dsimp` simplified rhs to\n        > {rhs'}",
    (rhsprf1, rhsprf2, ns) ← rhs'.simp {fail_if_unchanged := ff},
    when_tracing `simps.debug $ when (rhs' ≠ rhsprf1) trace!
      "[simps] > `simp` simplified rhs to\n        > {rhsprf1}",
    return (prod.mk rhsprf1 rhsprf2) }
    <|> prod.mk rhs <$> mk_app `eq.refl [type, lhs],
  eq_ap ← mk_mapp `eq $ [type, lhs, rhs].map some,
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := prf.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  when cfg.trace trace!
    "[simps] > adding projection {decl_name}:\n        > {decl_type}",
  decorate_error ("failed to add projection lemma " ++ decl_name.to_string ++ ". Nested error:") $
    add_decl decl,
  b ← succeeds $ is_def_eq lhs rhs,
  when (b ∧ `simp ∈ cfg.attrs) (set_basic_attribute `_refl_lemma decl_name tt),
  cfg.attrs.mmap' $ λ nm, set_attribute nm decl_name tt

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `to_apply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing lhs. -/
meta def simps_add_projections : Π (e : environment) (nm : name) (suffix : string)
  (type lhs rhs : expr) (args : list expr) (univs : list name) (must_be_str : bool)
  (cfg : simps_cfg) (todo : list string) (to_apply : list ℕ), tactic unit
| e nm suffix type lhs rhs args univs must_be_str cfg todo to_apply := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  when_tracing `simps.debug trace!
    "[simps] > Trying to add simp-lemmas for\n        > {lhs}
[simps] > Type of the expression before normalizing: {type}",
  (type_args, tgt) ← open_pis_whnf type cfg.type_md,
  when_tracing `simps.debug trace!"[simps] > Type after removing pi's: {tgt}",
  tgt ← whnf tgt,
  when_tracing `simps.debug trace!"[simps] > Type after reduction: {tgt}",
  let new_args := args ++ type_args,
  let lhs_ap := lhs.mk_app type_args,
  let rhs_ap := rhs.instantiate_lambdas_or_apps type_args,
  let str := tgt.get_app_fn.const_name,
  let new_nm := nm.append_suffix suffix,
  /- We want to generate the current projection if it is in `todo` -/
  let todo_next := todo.filter (≠ ""),
  /- Don't recursively continue if `str` is not a structure or if the structure is in
    `not_recursive`. -/
  if e.is_structure str ∧ ¬(todo = [] ∧ str ∈ cfg.not_recursive ∧ ¬must_be_str) then do
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    rhs_whnf ← whnf rhs_ap cfg.rhs_md,
    (rhs_ap, todo_now) ← -- `todo_now` means that we still have to generate the current simp lemma
      if h : ¬ is_constant_of rhs_ap.get_app_fn intro ∧
        is_constant_of rhs_whnf.get_app_fn intro then
      /- If this was a desired projection, we want to apply it before taking the whnf.
        However, if the current field is an eta-expansion (see below), we first want
        to eta-reduce it and only then construct the projection.
        This makes the flow of this function messy. -/
      when ("" ∈ todo ∧ to_apply = []) (if cfg.fully_applied then
        simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
        simps_add_projection new_nm type lhs rhs args univs cfg) >>
      return (rhs_whnf, ff) else
      return (rhs_ap, "" ∈ todo ∧ to_apply = []),
    if is_constant_of (get_app_fn rhs_ap) intro then do -- if the value is a constructor application
      tuples ← simps_get_projection_exprs e tgt rhs_ap cfg,
      when_tracing `simps.debug trace!"[simps] > Raw projection information:\n  {tuples}",
      let projs := tuples.map $ λ x, x.2.1,
      eta ← rhs_ap.is_eta_expansion, -- check whether `rhs_ap` is an eta-expansion
      let rhs_ap := eta.lhoare rhs_ap, -- eta-reduce `rhs_ap`
      /- As a special case, we want to automatically generate the current projection if `rhs_ap`
        was an eta-expansion. Also, when this was a desired projection, we need to generate the
        current projection if we haven't done it above. -/
      when (todo_now ∨ (todo = [] ∧ eta.is_some ∧ to_apply = [])) $
        if cfg.fully_applied then
          simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
          simps_add_projection new_nm type lhs rhs args univs cfg,
      /- If we are in the middle of a composite projection. -/
      when (to_apply ≠ []) $ do {
        (proj_expr, proj, new_rhs, proj_nrs, is_default) ← return $ tuples.inth to_apply.head,
        new_type ← infer_type new_rhs,
        simps_add_projections e nm suffix new_type lhs new_rhs new_args univs ff cfg todo
          to_apply.tail },
      /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
      automatically choose projections -/
      when ¬(to_apply ≠ [] ∨ todo = [""] ∨ (eta.is_some ∧ todo = [])) $ do
        let todo := if to_apply = [] then todo_next else todo,
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).is_prefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).is_prefix_of x).iget,
          simp_lemma := nm.append_suffix $ suffix ++ x,
          needed_proj := (x.split_on '_').tail.head in
          fail!
"Invalid simp-lemma {simp_lemma}. Structure {str} does not have projection {needed_proj}.
The known projections are:
  {projs}
You can also see this information by running
  `initialize_simps_projections? {str}`.
Note: these projection names might not correspond to the projection names of the structure.",
        tuples.mmap_with_index' $ λ proj_nr ⟨proj_expr, proj, new_rhs, proj_nrs, is_default⟩, do
          new_type ← infer_type new_rhs,
          let new_todo :=
            todo.filter_map $ λ x, x.get_rest ("_" ++ proj.last),
          -- we only continue with this field if it is non-propositional or mentioned in todo
          when ((is_default ∧ todo = []) ∨ new_todo ≠ []) $ do
            let new_lhs := proj_expr.instantiate_lambdas_or_apps [lhs_ap],
            let new_suffix := if cfg.short_name then "_" ++ proj.last else
              suffix ++ "_" ++ proj.last,
            when_tracing `simps.debug trace!"[simps] > Recursively add projections for: {new_lhs}",
            simps_add_projections e nm new_suffix new_type new_lhs new_rhs new_args univs
              ff cfg new_todo proj_nrs
    -- if I'm about to run into an error, try to set the transparency for `rhs_md` higher.
    else if cfg.rhs_md = transparency.none ∧ (must_be_str ∨ todo_next ≠ [] ∨ to_apply ≠ []) then do
      when cfg.trace trace!
        "[simps] > The given definition is not a constructor application:
        >   {rhs_ap}
        > Retrying with the options {{ rhs_md := semireducible, simp_rhs := tt}.",
      simps_add_projections e nm suffix type lhs rhs args univs must_be_str
        { rhs_md := semireducible, simp_rhs := tt, ..cfg} todo to_apply
    else do
      when (to_apply ≠ []) $
        fail!"Invalid simp-lemma {nm}.
The given definition is not a constructor application:\n  {rhs_ap}",
      when must_be_str $
        fail!"Invalid `simps` attribute. The body is not a constructor application:\n  {rhs_ap}",
      when (todo_next ≠ []) $
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ todo_next.head}.
The given definition is not a constructor application:\n  {rhs_ap}",
      if cfg.fully_applied then
        simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
        simps_add_projection new_nm type lhs rhs args univs cfg
  else do
    when must_be_str $
      fail!"Invalid `simps` attribute. Target {str} is not a structure",
    when (todo_next ≠ [] ∧ str ∉ cfg.not_recursive) $
        let first_todo := todo_next.head in
        fail!"Invalid simp-lemma {nm.append_suffix $ suffix ++ first_todo}.
Projection {(first_todo.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    if cfg.fully_applied then
      simps_add_projection new_nm tgt lhs_ap rhs_ap new_args univs cfg else
      simps_add_projection new_nm type lhs rhs args univs cfg

/-- `simps_tac` derives simp-lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
meta def simps_tac (nm : name) (cfg : simps_cfg := {}) (todo : list string := []) (trc := ff) :
  tactic unit :=
do
  e ← get_env,
  d ← e.get nm,
  let lhs : expr := const d.to_name d.univ_levels,
  let todo := todo.erase_dup.map $ λ proj, "_" ++ proj,
  b ← has_attribute' `to_additive nm,
  let cfg := if b then { attrs := cfg.attrs ++ [`to_additive], ..cfg } else cfg,
  let cfg := { trace := cfg.trace || is_trace_enabled_for `simps.verbose || trc, ..cfg },
  when (cfg.trace ∧ `to_additive ∈ cfg.attrs)
    trace!"[simps] > @[to_additive] will be added to all generated lemmas.",
  simps_add_projections e nm "" d.type lhs d.value [] d.univ_params tt cfg todo []

/-- The parser for the `@[simps]` attribute. -/
meta def simps_parser : parser (bool × list string × simps_cfg) := do
/- note: we don't check whether the user has written a nonsense namespace in an argument. -/
prod.mk <$> is_some <$> (tk "?")? <*>
  (prod.mk <$> many (name.last <$> ident) <*>
  (do some e ← parser.pexpr? | return {}, eval_pexpr simps_cfg e))

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

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)`.

* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
  * Exception: by default it will not recursively create simp-lemmas for fields in the structures
    `prod` and `pprod`. Give explicit projection names to override this behavior.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
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
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`, except that in this case it
  will not print projection information.
* Use `@[to_additive, simps]` to apply both `to_additive` and `simps` to a definition, making sure
  that `simps` comes after `to_additive`. This will also generate the additive versions of all
  simp-lemmas. Note however, that the additive versions of the simp-lemmas always use the default
  name generated by `to_additive`, even if a custom name is given for the additive version of the
  definition.
  -/

@[user_attribute] meta def simps_attr : user_attribute unit (bool × list string × simps_cfg) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simps_parser,
  after_set := some $
    λ n _ persistent, do
      guard persistent <|> fail "`simps` currently cannot be used as a local attribute",
      (trc, todo, cfg) ← simps_attr.get_param n,
      simps_tac n cfg todo trc }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  decl_names               := [`simps_attr],
  tags                     := ["simplification"] }

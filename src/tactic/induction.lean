/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.type_based_naming
import tactic.induction.util
import tactic.induction.unify_equations

open expr native tactic.interactive

namespace tactic
namespace eliminate

declare_trace eliminate_hyp

meta def trace_eliminate_hyp {α} [has_to_format α] (msg : thunk α) : tactic unit :=
when_tracing `eliminate_hyp $ trace $ to_fmt "eliminate_hyp: " ++ to_fmt (msg ())

meta def trace_state_eliminate_hyp {α} [has_to_format α] (msg : thunk α) :
  tactic unit := do
  state ← read,
  trace_eliminate_hyp $ format.join
    [to_fmt (msg ()), "\n-----\n", to_fmt state, "\n-----"]

@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)
(is_recursive : bool)

@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(non_param_args : list constructor_argument_info)
(num_non_param_args : ℕ)
(rec_args : list constructor_argument_info)
(num_rec_args : ℕ)

meta def constructor_info.num_nameable_arguments (c : constructor_info) : ℕ :=
c.num_non_param_args + c.num_rec_args

@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/--
`fuzzy_type_match t s` is true iff `t` and `s` are definitionally equal.
-/
-- TODO is it worth extending this check to be more permissive? E.g. if a
-- constructor argument has type `list α` and the index has type `list β`, we
-- may want to consider these types sufficiently similar to inherit the name.
-- Same (but even more obvious) with `vec α n` and `vec α (n + 1)`.
meta def fuzzy_type_match (t s : expr) : tactic bool :=
succeeds $ is_def_eq t s
-- (is_def_eq t s *> pure tt) <|> do
--   (some t_const) ← try_core $ get_app_fn_const_normalizing t | pure ff,
--   (some s_const) ← try_core $ get_app_fn_const_normalizing s | pure ff,
--   pure $ t_const = s_const

/-
TODO doc
Input: The local constants representing the constructor arguments.

Assumption: The input expression has the form `e = C x₁ ... xₙ` where
`C` is a local constant.

Output: A map associating each of the arg local constants `cᵢ` with the set of
indexes `j` such that `cᵢ` appears in `xⱼ` and `xⱼ`'s type fuzzily matches that
of `cᵢ`.
-/
meta def decompose_constructor_type_return (num_params : ℕ) (args : expr_set) :
  expr → tactic (rb_multimap expr ℕ) :=
λ ret_type, do
  ⟨_, ret_args⟩ ← decompose_app_normalizing ret_type,
  ret_args.mfoldl_with_index
    (λ i occ_map ret_arg, do
      if i < num_params
        then pure occ_map
        else do
          let ret_arg_consts := ret_arg.locals,
          ret_arg_consts.mfold occ_map $ λ c occ_map, do
            ret_arg_type ← infer_type ret_arg,
            eq ← fuzzy_type_match c.local_type ret_arg_type,
            pure $ if eq then occ_map.insert c i else occ_map)
    (mk_rb_multimap _ _)

/--
TODO doc
-/
meta def decompose_constructor_type (num_params : ℕ) (e : expr)
  : tactic (list (name × expr × bool × rb_set ℕ)) := do
  ⟨args, ret⟩ ← open_pis_normalizing e,
  let arg_constants := rb_map.set_of_list (args.map prod.fst),
  index_occs ← decompose_constructor_type_return num_params arg_constants ret,
  pure $ args.map $ λ ⟨c, dep⟩,
    let occs := (index_occs.find c).get_or_else mk_rb_map in
    ⟨c.local_pp_name, c.local_type, dep, occs⟩

/-- Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence. -/
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr) :
  bool :=
let base := arg_type.get_app_fn in
match base with
| (expr.const base _) := base = type_name
| _ := ff
end

/-- Gathers information about a constructor from the environment. Fails if `c`
does not refer to a constructor. -/
meta def get_constructor_info (env : environment) (iname : name)
  (num_params : ℕ) (c : name) : tactic constructor_info := do
  when (¬ env.is_constructor c) $ exceptional.fail format!
    "Expected {c} to be a constructor.",
  decl ← env.get c,
  args ← decompose_constructor_type num_params decl.type,
  let non_param_args := args.drop num_params,
  let non_param_args : list constructor_argument_info :=
    non_param_args.map_with_index $ λ i ⟨name, type, dep, index_occs⟩,
      let is_recursive := is_recursive_constructor_argument iname type in
      ⟨name, type, dep, index_occs.to_list, is_recursive⟩,
  let rec_args := non_param_args.filter $ λ ainfo, ainfo.is_recursive,
  pure
    { cname := decl.to_name,
      non_param_args := non_param_args,
      num_non_param_args := non_param_args.length,
      rec_args := rec_args,
      num_rec_args := rec_args.length
    }

/-- Gathers information about an inductive type from the environment. Fails if
`T` does not refer to an inductive type. -/
meta def get_inductive_info (env : environment) (T : name) :
  tactic inductive_info := do
  when (¬ env.is_inductive T) $ exceptional.fail format!
    "Expected {T} to be an inductive type.",
  decl ← env.get T,
  let type := decl.type,
  let num_params := env.inductive_num_params T,
  let num_indices := env.inductive_num_indices T,
  let constructor_names := env.constructors_of T,
  constructors ← constructor_names.mmap
    (get_constructor_info env T num_params),
  pure
    { iname := T,
      constructors := constructors,
      num_constructors := constructors.length,
      type := type,
      num_params := num_params,
      num_indices := num_indices }

meta structure eliminee_info :=
(ename : name)
(eexpr : expr)
(type : expr)
(args : rb_map ℕ expr)

-- Precond: eliminee is a local const.
meta def get_eliminee_info (eliminee : expr) : tactic eliminee_info := do
  type ← infer_type eliminee,
  ⟨f, args⟩ ← type.decompose_app_normalizing,
  pure
    { ename := eliminee.local_pp_name,
      eexpr := eliminee,
      type := type,
      args := args.to_rb_map }

meta structure constructor_argument_naming_info :=
(einfo : eliminee_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → tactic (list name)

meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule :=
λ i, if i.ainfo.is_recursive then pure [i.einfo.ename] else failed

meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule :=
λ i,
let index_occs := i.ainfo.index_occurrences in
let eliminee_args := i.einfo.args in
let local_index_instantiations :=
  (index_occs.map (eliminee_args.find >=> expr.local_names_option)).all_some in
-- TODO this needs to be updated when we allow complex indices
match local_index_instantiations with
| none := failed
| some [] := failed
| some ((uname, ppname) :: is) :=
  if is.all (λ ⟨uname', _⟩, uname' = uname)
    then pure [ppname]
    else failed
end

meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule :=
λ i,
let arg_name := i.ainfo.aname in
let arg_dep := i.ainfo.dependent in
if ! arg_dep && arg_name.is_likely_generated_name
  then failed
  else pure [arg_name]

meta def constructor_argument_naming_rule_type : constructor_argument_naming_rule :=
λ i, typical_variable_names i.ainfo.type

meta def constructor_argument_naming_rule_prop : constructor_argument_naming_rule :=
λ i, do
  (sort level.zero) ← infer_type i.ainfo.type,
  pure [`h]

meta def default_constructor_argument_name : name := `x

meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule) : tactic (list name) :=
first (rules.map ($ info)) <|> pure [default_constructor_argument_name]

meta def constructor_argument_names (info : constructor_argument_naming_info) :
  tactic (list name) :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named
  , constructor_argument_naming_rule_type
  , constructor_argument_naming_rule_prop ]

-- TODO this only works with simple names
meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

-- TODO the implementation is a bit of an 'orrible hack
meta def get_unused_name'_aux (n : name) (reserved : name_set) :
  option nat → tactic name :=
λ suffix, do
  n ← get_unused_name n suffix,
  if ¬ reserved.contains n
    then pure n
    else do
      let new_suffix :=
        match suffix with
        | none := some 1
        | some n := some (n + 1)
        end,
      get_unused_name'_aux new_suffix

meta def get_unused_name' (ns : list name) (reserved : name_set) : tactic name := do
  let fallback := match ns with | [] := `x | x :: _ := x end,
  (first $ ns.map $ λ n, do {
    guard (¬ reserved.contains n),
    fail_if_success (resolve_name n),
    pure n
  })
  <|>
  get_unused_name'_aux fallback reserved none

/- Precond: ns is nonempty. -/
meta def intro_fresh_reserved (ns : list name) (reserved : name_set) : tactic expr := do
  n ← get_unused_name' ns reserved,
  intro n

/- Precond: each of the name lists is nonempty. -/
meta def intro_lst_fresh_reserved (ns : list (name ⊕ list name)) (reserved : name_set) :
  tactic (list expr) := do
  let fixed := name_set.of_list $ ns.filter_map sum.get_left,
  let reserved := reserved.merge fixed,
  ns.mmap $ λ spec,
    match spec with
    | sum.inl n := intro n
    | sum.inr ns := intro_fresh_reserved ns reserved
    end

-- TODO integrate into tactic.rename?
-- Precond: each of the name lists in `renames` must be nonempty.
meta def rename_fresh (renames : name_map (list name)) (reserved : name_set) :
  tactic (name_map name) := do
  ctx ← revertible_local_context,
  let ctx_suffix := ctx.drop_while (λ h, (renames.find h.local_pp_name).is_none),
  let new_names :=
    ctx_suffix.map $ λ h,
      match renames.find h.local_pp_name with
      | none := sum.inl h.local_pp_name
      | some new_names := sum.inr new_names
      end,
  revert_lst ctx_suffix,
  new_hyps ← intro_lst_fresh_reserved new_names reserved,
  pure $ rb_map.of_list $
    list.map₂ (λ (old new : expr), (old.local_pp_name, new.local_pp_name))
      ctx_suffix new_hyps

/--
A value of `generalization_mode` describes the behaviour of the
auto-generalisation functionality:

- `generalize_all_except hs` means that the `hs` remain fixed and all other
  hypotheses are generalised. However, there are three exceptions:

  * Hypotheses depending on any `h` in `hs` also remain fixed. If we were to
    generalise them, we would have to generalise `h` as well.
  * Hypotheses which do not occur in the target and which do not mention the
    eliminee or its dependencies are never generalised. Generalising them would
    not lead to a more general induction hypothesis.
  * Frozen local instances and their dependencies are never generalised.

- `generalize_only hs` means that the only the `hs` are generalised. Exception:
  hypotheses which depend on the eliminee are generalised even if they do not
  appear in `hs`.
-/
@[derive has_reflect]
inductive generalization_mode
| generalize_all_except (hs : list name) : generalization_mode
| generalize_only (hs : list name) : generalization_mode

namespace generalization_mode

/--
Given the eliminee and a generalization_mode, this function returns the
unique names of the hypotheses that should be generalized. See
`generalization_mode` for what these are.
-/
meta def to_generalize (eliminee : expr) : generalization_mode → tactic name_set
| (generalize_only ns) := do
  eliminee_rev_deps ← kdependencies eliminee,
  -- TODO replace kdependencies with a variant that takes local defs into account
  let eliminee_rev_deps :=
    name_set.of_list $ eliminee_rev_deps.map local_uniq_name,
  ns ← ns.mmap (functor.map local_uniq_name ∘ get_local),
  pure $ eliminee_rev_deps.insert_list ns
| (generalize_all_except fixed) := do
  fixed ← fixed.mmap get_local,
  tgt ← target,
  let tgt_dependencies := tgt.local_unique_names,
  eliminee_type ← infer_type eliminee,
  eliminee_dependencies ← dependencies_of_local eliminee,
  fixed_dependencies ←
    name_set.merge_many <$> (eliminee :: fixed).mmap dependencies_of_local,
  ctx ← revertible_local_context,
  to_revert ← ctx.mmap_filter $ λ h, do {
    -- TODO what about local defs?
    h_depends_on_eliminee_deps ← local_depends_on_locals h eliminee_dependencies,
    let h_name := h.local_uniq_name,
    let rev :=
      ¬ fixed_dependencies.contains h_name ∧
      (h_depends_on_eliminee_deps ∨ tgt_dependencies.contains h_name),
    -- TODO I think `h_type.has_local_in eliminee_dependencies` is an
    -- overapproximation. What we actually want is any hyp that depends either
    -- on the eliminee or on one of the eliminee's index args. (But the
    -- overapproximation seems to work okay in practice as well.)
    pure $ if rev then some h_name else none
  },
  pure $ name_set.of_list to_revert

end generalization_mode

/--
Generalize hypotheses for the given eliminee and generalization mode. See
`generalization_mode` and `to_generalize`.
-/
meta def generalize_hyps (eliminee : expr) (gm : generalization_mode) : tactic ℕ := do
  to_revert ← gm.to_generalize eliminee,
  ⟨n, _⟩ ← revert_lst'' to_revert,
  pure n

meta def intron_fresh : ℕ → tactic (list expr)
| 0 := pure []
| (n + 1) := do
  nam ← mk_fresh_name,
  h ← intro nam,
  hs ← intron_fresh n,
  pure $ h :: hs

meta def constructor_intros (generate_induction_hyps : bool)
  (iinfo : inductive_info) (cinfo : constructor_info) :
  tactic (list (name × constructor_argument_info) × list (name × name)) := do
  let args := cinfo.non_param_args,
  arg_hyps ← intron_fresh cinfo.num_non_param_args,
  let arg_hyp_names :=
    list.map₂ (λ (h : expr) ainfo, (h.local_pp_name, ainfo)) arg_hyps args,
  tt ← pure generate_induction_hyps | pure (arg_hyp_names, []),

  let rec_args := arg_hyp_names.filter $ λ x, x.2.is_recursive,
  ih_hyps ← intron_fresh cinfo.num_rec_args,
  let ih_hyp_names :=
    list.map₂
      (λ (h : expr) (arg : name × constructor_argument_info),
        (h.local_pp_name, arg.1))
      ih_hyps rec_args,
  pure (arg_hyp_names, ih_hyp_names)

-- TODO spaghetti
meta def constructor_renames (generate_induction_hyps : bool)
  (einfo : eliminee_info) (iinfo : inductive_info) (cinfo : constructor_info)
  (with_names : list name) (args : list (name × constructor_argument_info))
  (ihs : list (name × name)) :
  tactic (list expr × list expr) := do
  -- Rename constructor arguments
  let iname := iinfo.iname,
  let ⟨args, with_names⟩ := args.zip_left' with_names,
  arg_renames : list (name × list name) ←
    args.mmap $ λ ⟨⟨old, ainfo⟩, with_name⟩, do {
      new ← constructor_argument_names ⟨einfo, iinfo, cinfo, ainfo⟩,
      let new :=
        match with_name with
        | some `_ := new
        | some with_name := [with_name]
        | none := new
        end,
      pure (old, new)
    },
  let arg_renames := rb_map.of_list arg_renames,
  new_arg_names ← rename_fresh arg_renames mk_name_set,
  new_arg_hyps ← args.mmap_filter $ λ ⟨⟨a, _⟩, _⟩, do {
    (some new_name) ← pure $ new_arg_names.find a | pure none,
    some <$> get_local new_name
  },

  -- Rename induction hypotheses (if we generated them)
  tt ← pure generate_induction_hyps | pure (new_arg_hyps, []),
  let ihs := ihs.zip_left with_names,
  ih_renames ← ihs.mmap $ λ ⟨⟨ih_hyp, arg_hyp⟩, with_name⟩, do {
    some arg_hyp ← pure $ new_arg_names.find arg_hyp
      | fail "internal error in constructor_renames",
    let new :=
      match with_name with
      | some `_ := sum.inr $ ih_name arg_hyp
      | some with_name := sum.inl with_name
      | none := sum.inr $ ih_name arg_hyp
      end,
    pure (ih_hyp, new)
  },
  let ih_renames : list (name × list name) :=
    -- Special case: When there's only one IH and it hasn't been named
    -- explicitly in a "with" clause, we call it simply "ih" (unless that name
    -- is already taken).
    match ih_renames with
    | [(h, sum.inr n)] := [(h, ["ih", n])]
    | ns := ns.map (λ ⟨h, n⟩, (h, [n.elim id id]))
    end,
  new_ih_names ← rename_fresh (rb_map.of_list ih_renames) mk_name_set,
  new_ih_hyps ← ihs.mmap_filter $ λ ⟨⟨a, _⟩, _⟩, do {
    (some new_name) ← pure $ new_ih_names.find a | pure none,
    some <$> get_local new_name
  },
  pure (new_arg_hyps, new_ih_hyps)

meta def structure_info (struct : name) : tactic (name × list name × ℕ) := do
  env ← get_env,
  fields ← env.structure_fields struct,
  let fields := fields.map $ λ f, struct ++ f,
  [constructor] ← pure $ env.constructors_of struct,
  let num_params := env.inductive_num_params struct,
  pure (constructor, fields, num_params)

meta def decompose_structure_value_aux : expr → expr →
  tactic (list (expr × expr) × name_set) :=
λ e f, do
  t ← infer_type e,
  ⟨struct, levels, params, constructor, fields, num_params⟩ ← do {
    ⟨const struct levels, params⟩ ← decompose_app_normalizing t,
    i ← structure_info struct,
    pure (struct, levels, params, i)
  }
  <|> fail! "decompose_structure_value: {e} : {t} is not a value of a structure",
  args ← do {
    ⟨const c _, args⟩ ← decompose_app_normalizing e,
    guard $ c = constructor,
    pure args
  }
  <|> fail!
    "decompose_structure_value: {e} is not an application of the structure constructor {constructor}",
  let args := (args.drop num_params).zip fields,
  rec ← args.mmap $ λ ⟨a, field⟩, do {
    let f := (const field levels).mk_app (params ++ [f]),
    rec ← try_core $ decompose_structure_value_aux a f,
    match rec with
    | some (es_fs, fields) := pure (es_fs, fields.insert field)
    | none := pure ([(a, f)], mk_name_set.insert field)
    end
  },
  let es_fs := (rec.map prod.fst).join,
  let fields := name_set.merge_many $ rec.map prod.snd,
  pure (es_fs, fields)

/--
If `e` is an application of a structure constructor, say `e = (x, y)`,
`decompose_structure_value` returns a list of fields:

    [(x, (x, y).fst), (y, (x, y).snd)]

This also works recursively: `(x, y, z)` yields

    [(x, (x, y, z).fst), (y, (x, y, z).snd.fst), (z, (x, y, z).snd.snd)]

Additionally, `decompose_structure_value` returns the fully qualified names of
all field accessors that appear in the output, e.g. `[prod.fst, prod.snd]` for
the above examples.

If `e` is not an application of a structure constructor, this tactic fails.
-/
meta def decompose_structure_value (e : expr) :
  tactic (list (expr × expr) × name_set) :=
decompose_structure_value_aux e e

meta def replace_structure_index_args (eliminee : expr) (index_args : list expr) :
  tactic name_set := do
  structure_args ←
    index_args.mmap_filter (try_core ∘ decompose_structure_value),
  let fields := name_set.merge_many $ structure_args.map prod.snd,
  let structure_args := (structure_args.map prod.fst).join,

  ctx ← revertible_local_context,
  eliminee_deps ← dependencies_of_local eliminee,
  relevant_ctx ← ctx.mfilter $ λ h, do {
    ff ← pure $ eliminee_deps.contains h.local_uniq_name | pure ff,
    H ← infer_type h,
    (structure_args.map prod.fst).many $ λ a, kdepends_on H a
  },
  n ← revert_lst relevant_ctx,
  tgt ← target,
  tgt ← structure_args.mfoldl (λ tgt ⟨e, f⟩, kreplace tgt e f) tgt,
  change tgt,
  intron n,
  pure fields

meta def generalize_complex_index_args_aux (eliminee : expr)
  (eliminee_head : expr) (eliminee_param_args eliminee_index_args : list expr)
  (generate_ihs : bool) : tactic (expr × list expr × ℕ × name_set) :=
focus1 $ do
  -- If any of the index arguments are values of a structure, e.g. `(x, y)`,
  -- replace `x` by `(x, y).fst` and `y` by `(x, y).snd` everywhere in the goal.
  -- This makes sure that when we abstract over `(x, y)`, we don't lose the
  -- connection to `x` and `y`.
  fields ← replace_structure_index_args eliminee eliminee_index_args,

  -- TODO Add equations only for complex index args (not all index args).
  -- This shouldn't matter semantically, but we'd get simpler terms.
  let js := eliminee_index_args,
  ctx ← revertible_local_context,
  tgt ← target,
  eliminee_deps ← dependencies_of_local eliminee,

  -- Revert the hypotheses which depend on the index args or the eliminee. We
  -- exclude dependencies of the eliminee because we can't replace their index
  -- occurrences anyway when we apply the recursor.
  relevant_ctx ← ctx.mfilter $ λ h, do {
    let dep_of_eliminee := eliminee_deps.contains h.local_uniq_name,
    dep_on_eliminee ← local_depends_on_local h eliminee,
    H ← infer_type h,
    dep_of_index ← js.many $ λ j, kdepends_on H j,
    -- TODO local defs
    pure $ (dep_on_eliminee ∧ h ≠ eliminee) ∨ (dep_of_index ∧ ¬ dep_of_eliminee)
  },
  ⟨relevant_ctx_size, relevant_ctx⟩ ← revert_lst' relevant_ctx,
  revert eliminee,

  -- Create the local constants that will replace the index args. We have to be
  -- careful to get the right types.
  let go : expr → list expr → tactic (list expr) :=
        λ j ks, do {
          J ← infer_type j,
          k ← mk_local' `index binder_info.default J,
          ks ← ks.mmap $ λ k', kreplace k' j k,
          pure $ k :: ks
        },
  ks ← js.mfoldr go [],

  let js_ks := js.zip ks,

  -- Replace the index args in the relevant context and the target.
  new_ctx ← relevant_ctx.mmap $ λ ⟨h, H⟩, do {
    H ← js_ks.mfoldr (λ ⟨j, k⟩ h, kreplace h j k) H,
    pure $ local_const h.local_uniq_name h.local_pp_name h.binding_info H
  },

  -- Replace the index args in the eliminee
  let new_eliminee_type := eliminee_head.mk_app (eliminee_param_args ++ ks),
  let new_eliminee :=
    local_const eliminee.local_uniq_name eliminee.local_pp_name
      eliminee.binding_info new_eliminee_type,

  -- Replace the index args in the target.
  new_tgt ← js_ks.mfoldr (λ ⟨j, k⟩ tgt, kreplace tgt j k) tgt,
  let new_tgt := new_tgt.pis (new_eliminee :: new_ctx),

  -- Generate the index equations and their proofs.
  let eq_name := if generate_ihs then `induction_eq else `cases_eq,
  let step2_input := js_ks.map $ λ ⟨j, k⟩, (eq_name, j, k),
  eqs_and_proofs ← generalizes.step2 reducible step2_input,
  let eqs := eqs_and_proofs.map prod.fst,
  let eq_proofs := eqs_and_proofs.map prod.snd,

  -- Assert the generalized goal and derive the current goal from it.
  generalizes.step3 new_tgt js ks eqs eq_proofs,

  -- Introduce the index variables and eliminee. The index equations
  -- and the relevant context remain reverted.
  let num_index_vars := js.length,
  index_vars ← intron' num_index_vars,
  index_equations ← intron' num_index_vars,
  eliminee ← intro1,
  revert_lst index_equations,
  pure (eliminee, index_vars, relevant_ctx_size, fields)

meta def generalize_complex_index_args (eliminee : expr) (num_params : ℕ)
  (generate_ihs : bool) : tactic (expr × ℕ × list name × name_set × ℕ) := do
  eliminee_type ← infer_type eliminee,
  ⟨eliminee_head, eliminee_args⟩ ← decompose_app_normalizing eliminee_type,
  let ⟨eliminee_param_args, eliminee_index_args⟩ :=
    eliminee_args.split_at num_params,

  ⟨eliminee, index_vars, num_generalized, fields⟩ ←
    generalize_complex_index_args_aux eliminee eliminee_head
      eliminee_param_args eliminee_index_args generate_ihs,
  let index_vars := index_vars.map local_pp_name,

  pure (eliminee, index_vars.length, index_vars, fields, num_generalized)

-- TODO spaghetti much
meta def ih_apps_aux : expr → list expr → ℕ → expr → tactic (expr × list expr)
| res cnsts 0       _ := pure (res, cnsts.reverse)
| res cnsts (n + 1) (pi pp_name binfo type e) := do
  match type with
  | (app (app (app (const `eq [u]) type') lhs) rhs) := do
    rhs_eq_lhs ← succeeds $ unify lhs rhs,
    if rhs_eq_lhs
      then do
        let arg := (const `eq.refl [u]) type' lhs,
        ih_apps_aux (app res arg) cnsts n e
      else do
        c ← mk_local' pp_name binfo type,
        ih_apps_aux (app res c) (c :: cnsts) n e
  | (app (app (app (app (const `heq [u]) lhs_type) lhs) rhs_type) rhs) := do
    types_eq ← succeeds $ is_def_eq lhs_type rhs_type,
    if ¬ types_eq
      then do
        c ← mk_local' pp_name binfo type,
        ih_apps_aux (app res c) (c :: cnsts) n e
      else do
        rhs_eq_lhs ← succeeds $ unify lhs rhs,
        if ¬ rhs_eq_lhs
          then do
            let type := (const `eq [u]) lhs_type lhs rhs,
            c ← mk_local' pp_name binfo type,
            let arg := (const `heq_of_eq [u]) lhs_type lhs rhs c,
            ih_apps_aux (app res arg) (c :: cnsts) n e
          else do
            let arg := (const `heq.refl [u]) lhs_type lhs,
            ih_apps_aux (app res arg) cnsts n e
  | _ := fail!
    "internal error in ih_apps_aux:\nexpected an equation, but got\n{type}"
  end
| _   _     _       e := fail!
  "internal error in ih_apps_aux:\nexpected a pi type, but got\n{e}"

meta def ih_apps (num_equations : ℕ) (ih : expr) (ih_type : expr) :
  tactic (expr × list expr) :=
ih_apps_aux ih [] num_equations ih_type

meta def assign_unassigned_mvar (mv : expr) (pp_name : name)
  (binfo : binder_info) : tactic (option expr) := do
  ff ← is_assigned mv | pure none,
  type ← infer_type mv,
  c ← mk_local' pp_name binfo type,
  unify mv c,
  pure c

meta def assign_unassigned_mvars (mvars : list (expr × name × binder_info)) :
  tactic (list expr) :=
mvars.mmap_filter $ λ ⟨mv, pp_name, binfo⟩,
  assign_unassigned_mvar mv pp_name binfo

meta def simplify_ih (num_generalized : ℕ) (num_index_vars : ℕ) (ih : expr) :
  tactic expr := do
  ih_type ← infer_type ih,
  ⟨generalized_arg_mvars, ih_type⟩ ← mopen_n_pis num_generalized ih_type,
  let apps := ih.app_of_list (generalized_arg_mvars.map prod.fst),
  ⟨apps, cnsts⟩ ← ih_apps num_index_vars apps ih_type,
  generalized_arg_locals ← assign_unassigned_mvars generalized_arg_mvars,
  apps ← instantiate_mvars apps,
  generalized_arg_locals ← generalized_arg_locals.mmap instantiate_mvars,
  cnsts ← cnsts.mmap instantiate_mvars,
  -- TODO implement a more efficient 'lambdas'
  let new_ih := apps.lambdas (generalized_arg_locals ++ cnsts),
  -- Sanity check to catch any errors in constructing new_ih.
  type_check new_ih <|> fail!
    "internal error in simplify_ih: constructed term does not type check:\n{new_ih}",
  replace' ih new_ih

/--
Returns the unique names of all hypotheses (local constants) in the context.
-/
-- TODO copied from init.meta.interactive
meta def hyp_unique_names : tactic name_set :=
do ctx ← local_context,
   pure $ ctx.foldl (λ r h, r.insert h.local_uniq_name) mk_name_set

/--
Returns all hypotheses (local constants) from the context except those whose
unique names are in `hyp_uids`.
-/
-- TODO copied from init.meta.interactive
meta def hyps_except (hyp_uids : name_set) : tactic (list expr) :=
do ctx ← local_context,
   pure $ ctx.filter (λ (h : expr), ¬ hyp_uids.contains h.local_uniq_name)

/--
  Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
-- TODO copied from init.meta.interactive
meta def set_cases_tags (in_tag : tag) (rs : list (name × list expr)) : tactic unit :=
do gs ← get_goals,
   match gs with
    -- if only one goal was produced, we should not make the tag longer
   | [g] := set_tag g in_tag
   | _   :=
     let tgs : list (name × list expr × expr) :=
       rs.map₂ (λ ⟨n, new_hyps⟩ g, ⟨n, new_hyps, g⟩) gs in
     tgs.mmap' $ λ ⟨n, new_hyps, g⟩, with_enable_tags $
        set_tag g $
          (case_tag.from_tag_hyps (n :: in_tag) (new_hyps.map expr.local_uniq_name)).render
   end

meta def unfold_only (to_unfold : list name) (e : expr) (fail_if_unchanged := tt) :
  tactic expr :=
simp_lemmas.dsimplify simp_lemmas.mk to_unfold e
  { eta := ff, zeta := ff, beta := ff, iota := ff
  , fail_if_unchanged := fail_if_unchanged }

meta def unfold_only_target (to_unfold : list name) (fail_if_unchanged := tt) :
  tactic unit := do
  tgt ← target,
  tgt ← unfold_only to_unfold tgt fail_if_unchanged,
  unsafe_change tgt

-- Note: frozen local instances.
-- Note: changes all unique names.
meta def unfold_only_everywhere (to_unfold : list name) (fail_if_unchanged := tt) :
  tactic unit := do
  n ← revert_all,
  unfold_only_target to_unfold fail_if_unchanged,
  intron n

-- TODO we should probably take the dependency closure of hyp_unique_names.
meta def revert_all_except (hyp_unique_names : name_set) : tactic ℕ := do
  ctx ← revertible_local_context,
  let ctx := ctx.filter (λ h, ¬ hyp_unique_names.contains h.local_uniq_name),
  revert_lst ctx

end eliminate

open eliminate

meta def eliminate_hyp (generate_ihs : bool) (eliminee : expr)
  (gm := generalization_mode.generalize_all_except [])
  (with_names : list name := []) : tactic unit :=
focus1 $ do
  einfo ← get_eliminee_info eliminee,
  let eliminee := einfo.eexpr,
  let eliminee_type := einfo.type,
  let eliminee_args := einfo.args.values.reverse,
  env ← get_env,

  -- Get info about the inductive type
  iname ← get_inductive_name eliminee_type <|> fail!
    "The type of {eliminee} should be an inductive type, but it is\n{eliminee_type}",
  iinfo ← get_inductive_info env iname,

  -- TODO We would like to disallow mutual/nested inductive types, since these
  -- have complicated recursors which we probably don't support. However, there
  -- seems to be no way to find out whether an inductive type is mutual/nested.
  -- (`environment.is_ginductive` doesn't seem to work.)

  trace_state_eliminate_hyp "State before complex index generalisation:",

  -- Generalise complex indices
  (eliminee, num_index_vars, index_var_names, structure_field_names, num_index_generalized) ←
    generalize_complex_index_args eliminee iinfo.num_params generate_ihs,

  trace_state_eliminate_hyp
    "State after complex index generalisation and before auto-generalisation:",

  -- Generalise hypotheses according to the given generalization_mode.
  num_auto_generalized ← generalize_hyps eliminee gm,
  let num_generalized := num_index_generalized + num_auto_generalized,

  -- NOTE: The previous step may have changed the unique names of all hyps in
  -- the context.

  -- Record the current case tag and the unique names of all hypotheses in the
  -- context.
  in_tag ← get_main_tag,
  old_hyps ← hyp_unique_names,

  trace_state_eliminate_hyp
    "State after auto-generalisation and before recursor application:",

  -- Apply the recursor. We first try the nondependent recursor, then the
  -- dependent recursor (if available).

  -- Construct a pexpr `@rec _ ... _ eliminee`. Why not ``(%%rec %%eliminee)?
  -- Because for whatever reason, `false.rec_on` takes the motive not as an
  -- implicit argument, like any other recursor, but as an explicit one.
  -- Why not something based on `mk_app` or `mk_mapp`? Because we need the
  -- special elaborator support for `elab_as_eliminator` definitions.
  let rec_app : name → pexpr := λ rec_suffix,
    (unchecked_cast expr.mk_app : pexpr → list pexpr → pexpr)
      (pexpr.mk_explicit (const (iname ++ rec_suffix) []))
      (list.repeat pexpr.mk_placeholder (eliminee_args.length + 1) ++
        [to_pexpr eliminee]),
  let rec_suffix := if generate_ihs then "rec_on" else "cases_on",
  let drec_suffix := if generate_ihs then "drec_on" else "dcases_on",
  interactive.apply (rec_app rec_suffix)
    <|> interactive.apply (rec_app drec_suffix)
    <|> fail! "Failed to apply the (dependent) recursor for {iname} on {eliminee}.",

  -- Prepare the "with" names for each constructor case.
  let with_names := prod.fst $
    with_names.take_lst
      (iinfo.constructors.map constructor_info.num_nameable_arguments),
  let constrs := iinfo.constructors.zip with_names,

  -- For each case (constructor):
  cases : list (option (name × list expr)) ←
    focus $ constrs.map $ λ ⟨cinfo, with_names⟩, do {
      trace_eliminate_hyp "============",
      trace_eliminate_hyp $ format! "Case {cinfo.cname}",
      trace_state_eliminate_hyp "Initial state:",

      -- Get the eliminee's arguments. (Some of these may have changed due to
      -- the generalising step above.)
      -- TODO propagate this information instead of re-parsing the type here?
      eliminee_type ← infer_type eliminee,
      (_, eliminee_args) ← decompose_app_normalizing eliminee_type,

      -- Clear the eliminated hypothesis (if possible)
      try $ clear eliminee,

      -- Clear the index args (unless other stuff in the goal depends on them)
      -- TODO is this the right thing to do? I don't think this necessarily
      -- preserves provability: The args we clear could contain interesting
      -- information, even if nothing else depends on them. Is there a way to
      -- avoid this, i.e. clean up even more conservatively?
      eliminee_args.mmap' (try ∘ clear),

      trace_state_eliminate_hyp
        "State after clearing the eliminee (and its arguments) and before unfolding structure projections:",

      -- Unfold structure projections which may have been introduced by the
      -- structure equation simplification step of generalize_complex_index_args.
      -- TODO This method reduces every occurrence of the given structure field
      -- projections, not only those which we actually introduced. This may
      -- yield some surprising results, but I don't see an easy way to prevent
      -- it.
      n ← revert_all_except old_hyps,
      unfold_only_target structure_field_names.to_list ff,
      intron n,

      trace_state_eliminate_hyp
        "State after unfolding structure projections and before introductions:",

      -- NOTE: The previous step invalidates all unique names (except those of
      -- the old hyps).

      -- Introduce the constructor arguments
      (constructor_arg_names, ih_names) ←
        constructor_intros generate_ihs iinfo cinfo,

      -- Introduce the auto-generalised hypotheses.
      intron num_auto_generalized,

      -- Introduce the index equations
      index_equations ← intron' num_index_vars,
      let index_equations := index_equations.map local_pp_name,

      -- Introduce the hypotheses that were generalised during index
      -- generalisation.
      intron num_index_generalized,

      trace_state_eliminate_hyp
        "State after introductions and before simplifying index equations:",

      -- Simplify the index equations. Stop after this step if the goal has been
      -- solved by the simplification.
      ff ← unify_equations index_equations
        | do {
            trace_eliminate_hyp "Case solved while simplifying index equations.",
            pure none
          },

      trace_state_eliminate_hyp
        "State after simplifying index equations and before simplifying IHs:",

      -- Simplify the induction hypotheses
      -- NOTE: The previous step may have changed the unique names of the
      -- induction hypotheses, so we have to locate them again. Their pretty
      -- names should be unique in the context, so we can use these.
      (ih_names.map prod.fst).mmap'
        (get_local >=> simplify_ih num_auto_generalized num_index_vars),

      trace_state_eliminate_hyp
        "State after simplifying IHs and before clearing index variables:",

      -- Try to clear the index variables. These often become unused during
      -- the index equation simplification step.
      index_var_names.mmap $ λ h, try (get_local h >>= clear),

      trace_state_eliminate_hyp
        "State after clearing index variables and before renaming:",

      -- Rename the constructor names and IHs. We do this here (rather than
      -- earlier, when we introduced them) because there may now be less
      -- hypotheses in the context, and therefore more of the desired
      -- names may be free.
      (constructor_arg_hyps, ih_hyps) ←
        constructor_renames generate_ihs einfo iinfo cinfo with_names
          constructor_arg_names ih_names,

      trace_state_eliminate_hyp "Final state:",

      -- Return the constructor name and the renamable new hypotheses. These are
      -- the hypotheses that can later be renamed by the `case` tactic. Note
      -- that index variables and index equations are not renamable. This may be
      -- counterintuitive in some cases, but it's surprisingly difficult to
      -- catch exactly the relevant hyps here.
      pure $ some (cinfo.cname, constructor_arg_hyps ++ ih_hyps)
    },

  set_cases_tags in_tag cases.reduce_option,

  pure ()

meta def eliminate_expr (generate_induction_hyps : bool) (eliminee : expr)
  (eq_name : option name := none) (gm := generalization_mode.generalize_all_except [])
  (with_names : list name := []) : tactic unit := do
  num_reverted ← revert_kdeps eliminee,
  -- TODO use revert_deps instead?
  hyp ← match eq_name with
      | some h := do
          x ← get_unused_name `x,
          interactive.generalize h () (to_pexpr eliminee, x),
          get_local x
      | none := do
          if eliminee.is_local_constant
            then pure eliminee
            else do
              x ← get_unused_name `x,
              generalize' eliminee x
      end,
  intron num_reverted,
  eliminate_hyp generate_induction_hyps hyp gm with_names

end tactic


namespace tactic.interactive

open tactic tactic.eliminate interactive interactive.types lean.parser

meta def generalisation_mode_parser : lean.parser generalization_mode :=
  (tk "fixing" *>
    ((tk "*" *> pure (generalization_mode.generalize_only []))
      <|>
      generalization_mode.generalize_all_except <$> many ident))
  <|>
  (tk "generalizing" *> generalization_mode.generalize_only <$> many ident)
  <|>
  pure (generalization_mode.generalize_all_except [])

precedence `fixing`:0

meta def induction' (eliminee : parse cases_arg_p)
  (gm : parse generalisation_mode_parser)
  (with_names : parse (optional with_ident_list)) : tactic unit := do
  let ⟨eq_name, e⟩ := eliminee,
  e ← to_expr e,
  eliminate_expr tt e eq_name gm (with_names.get_or_else [])

meta def cases' (eliminee : parse cases_arg_p)
  (with_names : parse (optional with_ident_list)) : tactic unit := do
  let ⟨eq_name, e⟩ := eliminee,
  e ← to_expr e,
  eliminate_expr ff e eq_name (generalization_mode.generalize_only [])
    (with_names.get_or_else [])

end tactic.interactive

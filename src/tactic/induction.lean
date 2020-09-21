/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.type_based_naming
import tactic.induction.util
import tactic.induction.unify_equations

open expr native

namespace tactic
namespace eliminate

--------------------------------------------------------------------------------
-- TRACING
--------------------------------------------------------------------------------

-- We set up two tracing functions to be used by `eliminate_hyp` and its
-- supporting tactics. Their output is enabled by setting `trace.eliminate_hyp`
-- to `true`.

declare_trace eliminate_hyp

meta def trace_eliminate_hyp {α} [has_to_format α] (msg : thunk α) : tactic unit :=
when_tracing `eliminate_hyp $ trace $ to_fmt "eliminate_hyp: " ++ to_fmt (msg ())

meta def trace_state_eliminate_hyp {α} [has_to_format α] (msg : thunk α) :
  tactic unit := do
  state ← read,
  trace_eliminate_hyp $ format.join
    [to_fmt (msg ()), "\n-----\n", to_fmt state, "\n-----"]

--------------------------------------------------------------------------------
-- INFORMATION GATHERING
--------------------------------------------------------------------------------

-- We define data structures for information relevant to the induction, and
-- functions to collect this information for a specific goal.

/--
Information about a constructor argument. Contains:

- `aname`: the argument's name.
- `type` : the argument's type.
- `dependent`: whether the argument is dependent, i.e. whether it occurs in the
  remainder of the constructor type.
- `index_occurrences`: the index arguments of the constructor's return type
  in which this argument occurs. If the constructor return type is
  `I i₀ ... iₙ` and the argument under consideration is `a`, and `a` occurs in
  `i₁` and `i₂`, then the `index_occurrences` are `1, 2`. As an additional
  requirement, for `iⱼ` to be considered an index occurrences,
  the type of `iⱼ` must match that of `a` according to
  `index_occurrence_type_match`.
- `is_recursive`: whether this is a recursive constructor argument.
-/
@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)
(is_recursive : bool)

/--
Information about a constructor. Contains:

- `cname`: the constructor's name.
- `non_param_args`: information about the arguments of the constructor,
  excluding the arguments induced by the parameters of the inductive type.
- `num_non_param_args`: the length of `non_param_args`.
- `rec_args`: the subset of `non_param_args` which are recursive constructor
  arguments.
- `num_rec_args`: the length of `rec_args`.

For example, take the constructor
```
list.cons : ∀ {α} (x : α) (xs : list α), list α
```
`α` is a parameter of `list`, so `non_param_args` contains information about `x`
and `xs`. `rec_args` contains information about `xs`.
-/
@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(non_param_args : list constructor_argument_info)
(num_non_param_args : ℕ)
(rec_args : list constructor_argument_info)
(num_rec_args : ℕ)

/--
When we construct the goal for the minor premise of a given constructor, this is
the number of hypotheses we must name.
-/
meta def constructor_info.num_nameable_hypotheses (c : constructor_info) : ℕ :=
c.num_non_param_args + c.num_rec_args

/--
Information about an inductive type. Contains:

- `iname`: the type's name.
- `constructors`: information about the type's constructors.
- `num_constructors`: the length of `constructors`.
- `type`: the type's type.
- `num_param`: the type's number of parameters.
- `num_indices`: the type's number of indices.
-/
@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/--
Information about an eliminee (i.e. the hypothesis on which we are performing
induction). Contains:

- `ename`: the eliminee's name.
- `eexpr`: the eliminee hypothesis.
- `type`: the type of `eexpr`.
- `args`: the eliminee's arguments. The eliminee has type `I x₀ ... xₙ`, where
  `I` is an inductive type. `args` is the map `[0 → x₀, ..., n → xₙ]`.
-/
-- TODO we should probably kill this since most of this information changes over
-- the course of the tactic. E.g. `eexpr` changes multiple times.
meta structure eliminee_info :=
(ename : name)
(eexpr : expr)
(type : expr)
(args : rb_map ℕ expr)

/--
`index_occurrence_type_match t s` is true iff `t` and `s` are definitionally
equal.
-/
-- We could extend this check to be more permissive. E.g. if a constructor
-- argument has type `list α` and the index has type `list β`, we may want to
-- consider these types sufficiently similar to inherit the name. Same (but even
-- more obvious) with `vec α n` and `vec α (n + 1)`.
meta def index_occurrence_type_match (t s : expr) : tactic bool :=
succeeds $ is_def_eq t s

/-
From the return type of a constructor `C` of an inductive type `I`, determine
the index occurrences of the constructor arguments of `C`.

Input:

- `num_params:` the number of parameters of `I`.
- `args`: a set of local constants representing the constructor arguments.
- `e`: the return type of `C` (with constructor arguments replaced by the local
  constants from `args`). `e` must be of the form `I x₁ ... xₙ`.

Output: A map associating each local constant `cᵢ` from `args` with the set of
indexes `j` such that `cᵢ` appears in `xⱼ` and `xⱼ`'s type fuzzily matches that
of `cᵢ`.
-/
meta def get_index_occurrences (num_params : ℕ) (args : expr_set) :
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
            eq ← index_occurrence_type_match c.local_type ret_arg_type,
            pure $ if eq then occ_map.insert c i else occ_map)
    (mk_rb_multimap _ _)

/--
Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence.
-/
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr) :
  bool :=
let base := arg_type.get_app_fn in
match base with
| (expr.const base _) := base = type_name
| _ := ff
end

/--
Get information about the arguments of a constructor `C` of an inductive type
`I`.

Input:

- `inductive_name`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `T`: the type of `C`.

Output: a `constructor_argument_info` structure for each argument of `C`.
-/
meta def get_constructor_argument_info (inductive_name : name)
  (num_params : ℕ) (T : expr) :
  tactic (list constructor_argument_info) := do
  ⟨args, ret⟩ ← open_pis_whnf_dep T,
  let arg_constants := rb_map.set_of_list (args.map prod.fst),
  index_occs ← get_index_occurrences num_params arg_constants ret,
  pure $ args.map $ λ ⟨c, dep⟩,
    let occs := (index_occs.find c).get_or_else mk_rb_map in
    let type := c.local_type in
    let is_recursive := is_recursive_constructor_argument inductive_name type in
    ⟨c.local_pp_name, type, dep, occs.to_list, is_recursive⟩

/--
Get information about a constructor `C` of an inductive type `I`.

Input:

- `iname`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `c` : the name of `C`.

Output:

A `constructor_info` structure for `C`.
-/
meta def get_constructor_info (iname : name) (num_params : ℕ) (c : name) :
  tactic constructor_info := do
  env ← get_env,
  when (¬ env.is_constructor c) $ fail! "Expected {c} to be a constructor.",
  decl ← env.get c,
  args ← get_constructor_argument_info iname num_params decl.type,
  let non_param_args := args.drop num_params,
  let rec_args := non_param_args.filter $ λ ainfo, ainfo.is_recursive,
  pure
    { cname := decl.to_name,
      non_param_args := non_param_args,
      num_non_param_args := non_param_args.length,
      rec_args := rec_args,
      num_rec_args := rec_args.length
    }

/--
Get information about an inductive type `I`, given `I`'s name.
-/
meta def get_inductive_info (I : name) : tactic inductive_info := do
  env ← get_env,
  when (¬ env.is_inductive I) $ fail! "Expected {I} to be an inductive type.",
  decl ← env.get I,
  let type := decl.type,
  let num_params := env.inductive_num_params I,
  let num_indices := env.inductive_num_indices I,
  let constructor_names := env.constructors_of I,
  constructors ← constructor_names.mmap
    (get_constructor_info I num_params),
  pure
    { iname := I,
      constructors := constructors,
      num_constructors := constructors.length,
      type := type,
      num_params := num_params,
      num_indices := num_indices }

/--
Get information about an eliminee. The eliminee must be a local hypothesis.
-/
meta def get_eliminee_info (eliminee : expr) : tactic eliminee_info := do
  type ← infer_type eliminee,
  ⟨f, args⟩ ← type.decompose_app_normalizing,
  pure
    { ename := eliminee.local_pp_name,
      eexpr := eliminee,
      type := type,
      args := args.to_rb_map }


--------------------------------------------------------------------------------
-- CONSTRUCTOR ARGUMENT NAMING
--------------------------------------------------------------------------------

-- This is the algorithm for naming constructor arguments.

/--
Information used when naming a constructor argument.
-/
meta structure constructor_argument_naming_info :=
(einfo : eliminee_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

/--
A constructor argument naming rule takes a `constructor_argument_naming_info`
structure and returns a list of suitable names for the argument. The list must
be nonempty. If the rule is not applicable to the given constructor argument, it
fails.
-/
-- TODO we should signal failure by returning the empty list.
@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → tactic (list name)

/--
Naming rule for recursive constructor arguments.
-/
meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule :=
λ i, if i.ainfo.is_recursive then pure [i.einfo.ename] else failed

/--
Naming rule for constructor arguments associated with an index.
-/
meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule :=
λ i,
let index_occs := i.ainfo.index_occurrences in
let eliminee_args := i.einfo.args in
let local_index_instantiations :=
  (index_occs.map (eliminee_args.find >=> expr.local_names_option)).all_some in
-- TODO this needs to be updated when we allow complex indices. Right now, the
-- rule only triggers if the eliminee arg is exactly a local const. We probably
-- want a more permissive rule where the eliminee arg can be an arbitrary term
-- as long as that term *contains* only a single local const.
match local_index_instantiations with
| none := failed
| some [] := failed
| some ((uname, ppname) :: is) :=
  if is.all (λ ⟨uname', _⟩, uname' = uname)
    then pure [ppname]
    else failed
end

/--
Naming rule for constructor arguments which are named in the constructor
declaration.
-/
meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule :=
λ i,
let arg_name := i.ainfo.aname in
let arg_dep := i.ainfo.dependent in
if ! arg_dep && arg_name.is_likely_generated_name
  then failed
  else pure [arg_name]

/--
Naming rule for constructor arguments whose type is associated with a list of
typical variable names. See `tactic.typical_variable_names`.
-/
meta def constructor_argument_naming_rule_type : constructor_argument_naming_rule :=
λ i, typical_variable_names i.ainfo.type

/--
Naming rule for constructor arguments whose type is `Prop`.
-/
-- TODO should be subsumed by the type-based naming rule.
meta def constructor_argument_naming_rule_prop : constructor_argument_naming_rule :=
λ i, do
  (sort level.zero) ← infer_type i.ainfo.type,
  pure [`h]

/--
Fallback constructor argument naming rule. This rule never fails.
-/
meta def constructor_argument_naming_rule_fallback : constructor_argument_naming_rule :=
λ _, pure [`x]

/--
`apply_constructor_argument_naming_rules info rules` applies the constructor
argument naming rules in `rules` to the constructor argument given by `info`.
Returns the result of the first rule that does not fail; fails if all rules
fail.
-/
meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule) : tactic (list name) :=
first $ rules.map ($ info)

/--
Get possible names for a constructor argument. This tactic applies all the
previously defined rules in order. It cannot fail and always returns a nonempty
list.
-/
meta def constructor_argument_names (info : constructor_argument_naming_info) :
  tactic (list name) :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named
  , constructor_argument_naming_rule_type
  , constructor_argument_naming_rule_prop
  , constructor_argument_naming_rule_fallback ]

/--
Introduce the new hypotheses generated by the minor premise for a given
constructor. The new hypotheses are given fresh (unique, non-human-friendly)
names. They are later renamed by `constructor_renames`. We delay the generation
of the human-friendly names because when `constructor_renames` is called, more
names may have become unused.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `iinfo`: information about the inductive type.
- `cinfo`: information about the constructor.

Output:

- For each constructor argument, the pretty name of the newly introduced
  hypothesis corresponding to the argument and its `constructor_argument_info`.
- For each newly introduced induction hypothesis, its pretty name and the name
  of the recursive constructor argument from which it was derived.
-/
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

/--
`ih_name arg_name` is the name `ih_<arg_name>`.
-/
meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

/--
Rename the new hypotheses in the goal for a minor premise.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `einfo`: information about the eliminee.
- `iinfo`: information about the inductive type.
- `cinfo`: information about the constructor whose minor premise we are
  processing.
- `with_names`: a list of names given by the user. These are used to name
  constructor arguments and induction hypotheses. Our own naming logic only
  kicks in if this list does not contain enough names.
- `args` and `ihs`: the output of `constructor_intros`.

Output:

- The newly introduced hypotheses corresponding to constructor arguments.
- The newly introduced induction hypotheses.
-/
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


--------------------------------------------------------------------------------
-- INDEX HYPOTHESIS GENERALISATION
--------------------------------------------------------------------------------

/-
The following functions are related to the generalisation of induction
hypotheses. By default, our tactic generalises all hypotheses to get the most
general induction hypotheses possible (with minor exceptions). Users can also,
however, choose to fix certain or all hypotheses.
-/

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

- `generalize_only hs` means that only the `hs` are generalised. Exception:
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
  fixed_dependencies ← (eliminee :: fixed).mmap dependencies_of_local,
  let fixed_dependencies := fixed_dependencies.foldl name_set.union mk_name_set,
  ctx ← revertible_local_context,
  to_revert ← ctx.mmap_filter $ λ h, do {
    -- TODO what about local defs?
    h_depends_on_eliminee_deps ← local_depends_on_locals h eliminee_dependencies,
    let h_name := h.local_uniq_name,
    let rev :=
      ¬ fixed_dependencies.contains h_name ∧
      (h_depends_on_eliminee_deps ∨ tgt_dependencies.contains h_name),
    -- TODO I think `h_depends_on_eliminee_deps` is an
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


--------------------------------------------------------------------------------
-- COMPLEX INDEX GENERALISATION
--------------------------------------------------------------------------------

/--
Generalise the complex index arguments.

Input:

- `eliminee`: the eliminee.
- `num_params`: the number of parameters of the inductive type.
- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).

Output:

- The new eliminee. This procedure may change the eliminee's type signature, so
  the old eliminee hypothesis is invalidated.
- The number of index placeholders we introduced.
- The index placeholder hypotheses we introduced.
- The number of hypotheses which were reverted because they contain complex
  indices.
-/
meta def generalize_complex_index_args (eliminee : expr) (num_params : ℕ)
  (generate_induction_hyps : bool) : tactic (expr × ℕ × list name × ℕ) :=
focus1 $ do
  eliminee_type ← infer_type eliminee,
  (eliminee_head, eliminee_args) ← decompose_app_normalizing eliminee_type,
  let ⟨eliminee_param_args, eliminee_index_args⟩ :=
    eliminee_args.split_at num_params,

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

  -- Replace the index args in the relevant context.
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
  let eq_name := if generate_induction_hyps then `induction_eq else `cases_eq,
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

  let index_vars := index_vars.map local_pp_name,
  pure (eliminee, index_vars.length, index_vars, relevant_ctx_size)


--------------------------------------------------------------------------------
-- INDUCTION HYPOTHESIS SIMPLIFICATION
--------------------------------------------------------------------------------

-- The following functions simplify induction hypotheses by instantiating index
-- placeholders and removing redundant index equations.

-- TODO spaghetti much
private meta def ih_apps_aux : expr → list expr → ℕ → expr → tactic (expr × list expr)
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

/--
Given an induction hypothesis `ih` of the form

```
ih : Hi₁ = i₁ → ... → Hiₙ = iₙ → P
```

where the leading equations are index equations, this tactic creates a proof
`p : P` in a new context `Γ`. `Γ` contains a subset of the index equations.
Equations whose left-hand and right-hand sides can be unified are deleted, i.e.
they do not appear in `Γ`.

Input:

- `num_equations`: the number of index equations.
- `ih`: the induction hypothesis.
- `ih_type`: the type of `ih`.

Output:

The proof `p` and context `Γ` as described above. `Γ` is given as a list of
local constants.
-/
meta def ih_apps (num_equations : ℕ) (ih : expr) (ih_type : expr) :
  tactic (expr × list expr) :=
ih_apps_aux ih [] num_equations ih_type

/--
`assign_local_to_unassigned_mvar mv pp_name binfo`, where `mv` is a
metavariable, acts as follows:

- If `mv` is assigned, it is not changed and the tactic returns `none`.
- If `mv` is not assigned, it is assigned a fresh local constant with
  the type of `mv`, pretty name `pp_name` and binder info `binfo`. This local
  constant is returned.
-/
meta def assign_local_to_unassigned_mvar (mv : expr) (pp_name : name)
  (binfo : binder_info) : tactic (option expr) := do
  ff ← is_assigned mv | pure none,
  type ← infer_type mv,
  c ← mk_local' pp_name binfo type,
  unify mv c,
  pure c

/--
Apply `assign_local_to_unassigned_mvar` to a list of metavariables. Returns the
newly created local constants.
-/
meta def assign_locals_to_unassigned_mvars
  (mvars : list (expr × name × binder_info)) : tactic (list expr) :=
mvars.mmap_filter $ λ ⟨mv, pp_name, binfo⟩,
  assign_local_to_unassigned_mvar mv pp_name binfo

/--
Simplify an induction hypothesis.
-/
meta def simplify_ih (num_generalized : ℕ) (num_index_vars : ℕ) (ih : expr) :
  tactic expr := do
  ih_type ← infer_type ih,
  (generalized_arg_mvars, ih_type) ← open_n_pis_metas' ih_type num_generalized,
  let apps := ih.app_of_list (generalized_arg_mvars.map prod.fst),
  ⟨apps, cnsts⟩ ← ih_apps num_index_vars apps ih_type,
  generalized_arg_locals ←
    assign_locals_to_unassigned_mvars generalized_arg_mvars,
  apps ← instantiate_mvars apps,
  generalized_arg_locals ← generalized_arg_locals.mmap instantiate_mvars,
  cnsts ← cnsts.mmap instantiate_mvars,
  -- TODO implement a more efficient 'lambdas'
  let new_ih := apps.lambdas (generalized_arg_locals ++ cnsts),
  -- Sanity check to catch any errors in constructing new_ih.
  type_check new_ih <|> fail!
    "internal error in simplify_ih: constructed term does not type check:\n{new_ih}",
  ih' ← note ih.local_pp_name none new_ih,
  clear ih,
  pure ih'

end eliminate


--------------------------------------------------------------------------------
-- THE ELIMINATION TACTIC
--------------------------------------------------------------------------------

open eliminate

/--
`eliminate_hyp generate_ihs eliminee gm with_names` performs induction or case
analysis on the hypothesis `eliminee`. If `generate_ihs` is true, the tactic
performs induction, otherwise case analysis.

In case analysis mode, `eliminate_hyp` is very similar to `tactic.cases`. The
only differences (assuming no bugs in `eliminate_hyp`) are that `eliminate_hyp`
can do case analysis on a slightly larger class of hypotheses and that it
generates more human-friendly names.

In induction mode, `eliminate_hyp` is similar to `tactic.induction`, but with
more significant differences:

- If the eliminee (the hypothesis we are performing induction on) has complex
  indices, `eliminate_hyp` 'remembers' them. A complex expression is any
  expression that is not merely a local hypothesis. An eliminee
  `e : I p₁ ... pₙ j₁ ... jₘ`, where `I` is an inductive type with `n`
  parameters and `m` indices, has a complex index if any of the `jᵢ` are
  complex. In this situation, standard `induction` effectively forgets the exact
  values of the complex indices, which often leads to unprovable goals.
  `eliminate_hyp` 'remembers' them by adding propositional equalities. As a
  result, you may find equalities named `induction_eq` in your goal, and the
  induction hypotheses may also quantify over additional equalities.
- `eliminate_hyp` generalises induction hypotheses as much as possible by
  default. This means that if you eliminate `n` in the goal
  ```
  n m : ℕ
  ⊢ P n m
  ```
  the induction hypothesis is `∀ m, P n m` instead of `P n m`.

  You can modify this behaviour by giving a different generalisation mode `gm`;
  see `tactic.eliminate.generalization_mode`.
- `eliminate_hyp` generates much more human-friendly names than `induction`. It
  also clears more redundant hypotheses.
- `eliminate_hyp` currently does not support custom induction principles a la
  `induction using`.

If `with_names` is nonempty, `eliminate_hyp` uses the given names for the new
hypotheses it introduces (like `cases with` and `induction with`).
-/
meta def eliminate_hyp (generate_ihs : bool) (eliminee : expr)
  (gm := generalization_mode.generalize_all_except [])
  (with_names : list name := []) : tactic unit :=
focus1 $ do
  -- TODO make sure that the eliminee is not a local def.
  einfo ← get_eliminee_info eliminee,
  let eliminee := einfo.eexpr,
  let eliminee_type := einfo.type,
  let eliminee_args := einfo.args.values.reverse,
  env ← get_env,

  -- Get info about the inductive type
  iname ← get_inductive_name eliminee_type <|> fail!
    "The type of {eliminee} should be an inductive type, but it is\n{eliminee_type}",
  iinfo ← get_inductive_info iname,

  -- TODO We would like to disallow mutual/nested inductive types, since these
  -- have complicated recursors which we probably don't support. However, there
  -- seems to be no way to find out whether an inductive type is mutual/nested.
  -- (`environment.is_ginductive` doesn't seem to work.)

  trace_state_eliminate_hyp "State before complex index generalisation:",

  -- Generalise complex indices
  (eliminee, num_index_vars, index_var_names, num_index_generalized) ←
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
      (iinfo.constructors.map constructor_info.num_nameable_hypotheses),
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
        "State after clearing the eliminee (and its arguments) and before introductions:",

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

/--
A variant of `tactic.eliminate_hyp` which performs induction or case analysis on
an arbitrary expression. `eliminate_hyp` requires that the eliminee is a
hypothesis. `eliminate_expr` lifts this restriction by generalising the goal
over the eliminee before calling `eliminate_hyp`. The generalisation replaces
the eliminee with a new hypothesis `x` everywhere in the goal. If `eq_name` is
`some h`, an equation `h : eliminee = x` is added to remember the value of the
eliminee.
-/
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

/--
Parse a `fixing` or `generalizing` clause for `induction'` or `cases'`.
-/
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

/--
A variant of `tactic.interactive.induction`, with the following differences:

- If the eliminee (the hypothesis we are performing induction on) has complex
  indices, `eliminate_hyp` 'remembers' them. A complex expression is any
  expression that is not merely a local hypothesis. An eliminee
  `e : I p₁ ... pₙ j₁ ... jₘ`, where `I` is an inductive type with `n`
  parameters and `m` indices, has a complex index if any of the `jᵢ` are
  complex. In this situation, standard `induction` effectively forgets the exact
  values of the complex indices, which often leads to unprovable goals.
  `eliminate_hyp` 'remembers' them by adding propositional equalities. As a
  result, you may find equalities named `induction_eq` in your goal, and the
  induction hypotheses may also quantify over additional equalities.
- `eliminate_hyp` generalises induction hypotheses as much as possible by
  default. This means that if you eliminate `n` in the goal
  ```
  n m : ℕ
  ⊢ P n m
  ```
  the induction hypothesis is `∀ m, P n m` instead of `P n m`.
- `eliminate_hyp` generates much more human-friendly names than `induction`. It
  also clears redundant hypotheses more aggressively.
- `eliminate_hyp` currently does not support custom induction principles a la
  `induction using`.

Like `induction`, `induction'` supports some modifiers:

`induction' e with n₁ ... nₘ` uses the names `nᵢ` for the new hypotheses.

`induction' e fixing h₁ ... hₙ` fixes the hypotheses `hᵢ`, so the induction
hypothesis is not generalised over these hypotheses.

`induction' e fixing *` fixes all hypotheses. This disables the generalisation
functionality, so this mode behaves like standard `induction`.

`induction' e generalizing h₁ ... hₙ` generalises only the hypotheses `hᵢ`. This
mode behaves like `induction e generalising h₁ ... hₙ`.

`induction' t`, where `t` is an arbitrary term (rather than a hypothesis),
generalises the goal over `t`, then performs induction on the generalised goal.

`induction' h : t = x` is similar, but also adds an equation `h : t = x` to
remember the value of `t`.
-/
meta def induction' (eliminee : parse cases_arg_p)
  (gm : parse generalisation_mode_parser)
  (with_names : parse (optional with_ident_list)) : tactic unit := do
  let ⟨eq_name, e⟩ := eliminee,
  e ← to_expr e,
  eliminate_expr tt e eq_name gm (with_names.get_or_else [])

/--
A variant of `tactic.interactive.cases`, with minor changes:

- `cases'` can perform case analysis on some (rare) goals that `cases` does not
  support.
- `cases'` generates much more human-friendly names for the new hypotheses it
  introduces.

This tactic supports the same modifiers as `cases`, e.g.
```
cases' H : e = x with n m o
```

This is almost exactly the same as `tactic.interactive.induction'`, only that no
induction hypotheses are generated.
-/
meta def cases' (eliminee : parse cases_arg_p)
  (with_names : parse (optional with_ident_list)) : tactic unit := do
  let ⟨eq_name, e⟩ := eliminee,
  e ← to_expr e,
  eliminate_expr ff e eq_name (generalization_mode.generalize_only [])
    (with_names.get_or_else [])

end tactic.interactive

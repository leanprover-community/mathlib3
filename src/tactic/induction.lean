/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import control.basic data.sum data.list.defs tactic.basic
import tactic.generalizes tactic.linarith tactic.type_based_naming

/--
After elaboration, Lean does not have non-dependent function types with
unnamed arguments. This means that for the declaration

```lean
inductive test : Type :=
| intro : unit → test
```

the type of `test.intro` becomes

```lean
test.intro : ∀ (a : unit), test
```lean

after elaboration, where `a` is an auto-generated name.

This means that we can't know for sure whether a constructor argument was named
by the user. Hence the following hack: If an argument is non-dependent *and* its
name is `a` or `a_n` for some `n ∈ ℕ`, then we assume that this name was
auto-generated rather than chosen by the user.
-/
library_note "unnamed constructor arguments"


universes u v w


namespace list

open native

variables {α : Type u} {β : Type v}

/-- Auxiliary definition for `foldl_with_index`. -/
def foldl_with_index_aux (f : ℕ → α → β → α) : ℕ → α → list β → α
| _ a [] := a
| i a (b :: l) := foldl_with_index_aux (i + 1) (f i a b) l

/--
Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index.
-/
def foldl_with_index (f : ℕ → α → β → α) (a : α) (l : list β) : α :=
foldl_with_index_aux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldr_with_index_aux (f : ℕ → α → β → β) : ℕ → β → list α → β
| _ b [] := b
| i b (a :: l) := f i a (foldr_with_index_aux (i + 1) b l)

/--
Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index.
-/
def foldr_with_index (f : ℕ → α → β → β) (b : β) (l : list α) : β :=
foldr_with_index_aux f 0 b l

section mfold_with_index

variables {m : Type v → Type w} [monad m]

/-- Monadic variant of `foldl_with_index`. -/
def mfoldl_with_index (f : ℕ → β → α → m β) (b : β) (as : list α) : m β :=
as.foldl_with_index (λ i ma b, do a ← ma, f i a b) (pure b)

/-- Monadic variant of `foldr_with_index`. -/
def mfoldr_with_index (f : ℕ → α → β → m β) (b : β) (as : list α) : m β :=
as.foldr_with_index (λ i a mb, do b ← mb, f i a b) (pure b)

end mfold_with_index

section mmap_with_index

variables {m : Type v → Type w} [applicative m]

def mmap_with_index_aux (f : ℕ → α → m β) : ℕ → list α → m (list β)
| _ [] := pure []
| i (a :: as) := list.cons <$> f i a <*> mmap_with_index_aux (i + 1) as

def mmap_with_index (f : ℕ → α → m β) (as : list α) : m (list β) :=
mmap_with_index_aux f 0 as

end mmap_with_index

section mmap_with_index'

variables {m : Type → Type v} [applicative m]

def mmap_with_index'_aux (f : ℕ → α → m unit) : ℕ → list α → m unit
| _ [] := pure ()
| i (a :: as) := f i a *> mmap_with_index'_aux (i + 1) as

def mmap_with_index' (f : ℕ → α → m unit) (as : list α) : m unit :=
mmap_with_index'_aux f 0 as

end mmap_with_index'

def to_rbmap : list α → rbmap ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) (mk_rbmap ℕ α)

meta def to_rb_map {α : Type} : list α → rb_map ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) mk_rb_map

def all_some : list (option α) → option (list α)
| [] := some []
| (some x :: xs) := (λ xs, x :: xs) <$> all_some xs
| (none :: xs) := none

def mbfind' {m : Type u → Type v} [monad m] {α : Type u} (p : α → m (ulift bool))
  : list α → m (option α)
| [] := pure none
| (x :: xs) := do
  ⟨px⟩ ← p x,
  if px then pure (some x) else mbfind' xs

def mbfind {m : Type → Type v} [monad m] {α : Type} (p : α → m bool)
  (xs : list α) : m (option α) :=
xs.mbfind' (functor.map ulift.up ∘ p)

-- I'd like to define this in terms of mbfind, but that gives us less universe
-- polymorphism.
def mbany {m : Type → Type v} [monad m] {α : Type u} (p : α → m bool)
  : list α → m bool
| [] := pure ff
| (x :: xs) := do
  px ← p x,
  if px then pure tt else mbany xs

def mball {m} [monad m] {α} (p : α → m bool) (xs : list α) : m bool :=
bnot <$> xs.mbany (functor.map bnot ∘ p)

def mbor {m} [monad m] (xs : list (m bool)) : m bool := xs.mbany id

def mband {m} [monad m] (xs : list (m bool)) : m bool := xs.mball id

def mfilter_map {m : Type u → Type v} [monad m] {α β} (p : α → m (option β))
  : list α → m (list β)
| [] := pure []
| (a :: as) := do
  mb ← p a,
  match mb with
  | some b := (λ bs, b :: bs) <$> mfilter_map as
  | none := mfilter_map as
  end

end list


namespace native

@[reducible] meta def rb_multimap (α β : Type) : Type :=
rb_map α (rb_set β)

meta def mk_rb_multimap (α β : Type) [ltα : has_lt α] [ltβ : has_lt β]
  [decidable_rel ((<) : α → α → Prop)]
  : rb_multimap α β :=
mk_rb_map


namespace rb_multimap

variables {α β : Type}

section

variables [has_lt α] [has_lt β] [decidable_rel ((<) : α → α → Prop)]

meta def find (m : rb_multimap α β) (a : α)
  : option (rb_set β) :=
rb_map.find m a

variables [decidable_rel ((<) : β → β → Prop)]

meta def insert (m : rb_multimap α β) (a : α) (b : β) : rb_multimap α β :=
let bs := m.find a in
rb_map.insert m a
  (match bs with
   | none := rb_map.set_of_list [b]
   | (some bs) := bs.insert b
   end)

meta def contains (m : rb_multimap α β) (a : α) (b : β) : bool :=
match m.find a with
| none := false
| (some bs) := bs.contains b
end

end

meta def to_list (m : rb_multimap α β) : list (α × rb_set β) :=
rb_map.to_list m

meta def to_multilist (m : rb_multimap α β) : list (α × list β) :=
(rb_map.to_list m).map (λ ⟨a, bs⟩, ⟨a, bs.to_list⟩)

end rb_multimap


namespace rb_set

variables {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)]

meta def merge (xs ys : rb_set α) : rb_set α :=
rb_set.fold ys xs (λ a xs, xs.insert a)

meta def merge_many (xs : list (rb_set α)) : rb_set α :=
xs.foldl merge mk_rb_set

end rb_set

end native

open native


namespace name_set

meta def merge (xs ys : name_set) : name_set :=
name_set.fold ys xs (λ a xs, xs.insert a)

meta def merge_many (xs : list name_set) : name_set :=
xs.foldl merge mk_name_set

end name_set


namespace expr

meta def local_names_option : expr → option (name × name)
| (local_const n₁ n₂ _ _) := some (n₁, n₂)
| _ := none

/-- Given a closed type of the form `∀ (x : T) ... (z : U), V`, this function
returns a tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.

Note that the type of each argument and the return type all live in a different
contexts. For example, for the input `∀ (x : α) (y : β x) (z : γ x y), δ`,
`decompose_pi` returns `β #0` as the type of `y` and `γ #1 #0` as the type of
`z` -- the two `#0`s do not denote the same thing.
-/
meta def decompose_pi
  : expr → list (name × binder_info × expr × bool) × ℕ × expr
| (pi name binfo T rest) :=
  let (args, n_args, ret) := decompose_pi rest in
  -- NOTE: the following makes this function quadratic in the size of the input
  -- expression.
  let dep := rest.has_var_idx 0 in
  ((name, binfo, T, dep) :: args, n_args + 1, ret)
| e := ([], 0, e)

/-- Given a closed type of the form `∀ (x : T) ... (z : U), V`, this function
returns a tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.

The input expression is normalised lazily. This means that the returned
expressions are not necessarily in normal form.

Note that the type of each argument and the return type all live in a different
contexts. For example, for the input `∀ (x : α) (y : β x) (z : γ x y), δ`,
`decompose_pi_normalizing` returns `β #0` as the type of `y` and `γ #1 #0`
as the type of `z` -- the two `#0`s do not denote the same thing.
-/
meta def decompose_pi_normalizing
  : expr → tactic (list (name × binder_info × expr × bool) × expr) := λ e, do
  e ← tactic.whnf e,
  match e with
  | (pi n binfo T rest) := do
      (args, ret) ← decompose_pi_normalizing rest,
      -- NOTE: the following makes this function quadratic in the size of the input
      -- expression.
      let dep := rest.has_var_idx 0,
      pure ((n , binfo, T, dep) :: args, ret)
  | _ := pure ([] , e)
  end

meta def recompose_pi (binders : list (name × binder_info × expr)) (ret : expr)
  : expr :=
binders.foldr (λ ⟨name, info, t⟩ acc, pi name info t acc) ret

/-- Auxiliary function for `decompose_app`. -/
meta def decompose_app_aux : expr → expr × list expr
| (app t u) :=
  let (f, args) := decompose_app_aux t in
  (f, u :: args)
| e := (e, [])

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.
-/
meta def decompose_app (e : expr) : expr × list expr :=
let (f , args) := decompose_app_aux e in
(f , args.reverse)

/-- Auxiliary function for `decompose_app_normalizing`. -/
meta def decompose_app_normalizing_aux (md : tactic.transparency)
  : expr → tactic (expr × list expr) := λ e, do
  e ← tactic.whnf e md,
  match e with
  | (app t u) := do
      (f , args) ← decompose_app_normalizing_aux t,
      pure (f, u :: args)
  | _ := pure (e, [])
  end

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.

`e` is normalised lazily. This means that the returned expressions are not
necessarily in normal form.
-/
meta def decompose_app_normalizing (e : expr) (md := semireducible)
  : tactic (expr × list expr) := do
  (f , args) ← decompose_app_normalizing_aux md e,
  pure (f , args.reverse)

meta def locals (e : expr) : expr_set :=
e.fold mk_expr_set $ λ e _ occs,
  if e.is_local_constant
    then occs.insert e
    else occs

meta def local_unique_names (e : expr) : name_set :=
e.fold mk_name_set $ λ e _ occs,
  match e with
  | (local_const u _ _ _) := occs.insert u
  | _ := occs
  end

meta def match_eq : expr → option (level × expr × expr × expr)
| (app (app (app (const `eq [u]) type) lhs) rhs) := some (u, type, lhs, rhs)
| _ := none

meta def match_heq : expr → option (level × expr × expr × expr × expr)
| (app (app (app (app (const `heq [u]) lhs_type) lhs) rhs_type) rhs) :=
  some (u, lhs_type, lhs, rhs_type, rhs)
| _ := none

end expr


namespace sum

def get_left {α β} : α ⊕ β → option α
| (inl a) := some a
| _ := none

def get_right {α β} : α ⊕ β → option β
| (inr b) := some b
| _ := none

def is_left {α β} : α ⊕ β → bool
| (inl _) := tt
| (inr _) := ff

def is_right {α β} : α ⊕ β → bool
| (inl _) := ff
| (inr _) := tt

end sum


namespace name

open parser

meta def basename : name → name
| anonymous := anonymous
| (mk_string s _) := mk_string s anonymous
| (mk_numeral n _) := mk_numeral n anonymous

/-- See [note unnamed constructor arguments]. -/
meta def likely_generated_name_p : parser unit := do
  ch 'a',
  optional (ch '_' *> nat),
  pure ()

/-- See [note unnamed constructor arguments]. -/
meta def is_likely_generated_name (n : name) : bool :=
match n with
| anonymous := ff
| mk_numeral _ _ := ff
| mk_string s anonymous := (likely_generated_name_p.run_string s).is_right
| mk_string _ _ := ff
end

end name


namespace tactic

open expr native tactic.interactive

meta def mopen_binder_aux (type e : expr) : tactic (expr × expr) := do
  mv ← mk_meta_var type,
  pure $ (mv, e.instantiate_var mv)

meta def mopen_pi : expr → tactic (expr × name × binder_info × expr)
| (pi pp_name binfo type e) := do
  ⟨mv, e⟩ ← mopen_binder_aux type e,
  pure (mv, pp_name, binfo, e)
| e := fail! "mopen_pi: expected an expression starting with a pi, but got\n{e}"

meta def mopen_n_pis : ℕ → expr → tactic (list (expr × name × binder_info) × expr)
| 0 e := pure ([], e)
| (n + 1) e := do
  ⟨mv, pp_name, binfo, e⟩ ← mopen_pi e,
  ⟨args, u⟩ ← mopen_n_pis n e,
  pure $ ((mv, pp_name, binfo) :: args, u)

meta def open_binder_aux (pp_name : name) (bi : binder_info) (t e : expr)
  : tactic (expr × expr) := do
  c ← mk_local' pp_name bi t,
  pure $ (c, e.instantiate_var c)

/--
Given an `e` with `e = ∀ (x : T), U`, `open_pi e` returns

- `c`, a new local constant with type `T` (and the same pretty name and binder
  info as the binder for `x`).
- `U[x/c]`.

Note that `c` is not introduced into the context, so `U[x/c]` will not
type-check.

Fails if `e` does not start with a pi.
-/
meta def open_pi : expr → tactic (expr × expr)
| (pi n bi t e) := open_binder_aux n bi t e
| e := fail! "open_pi: expected an expression starting with a pi, but got\n{e}"

-- TODO could be more efficient: open_binder uses instantiate_var once per
-- binder, so the expression is traversed a lot. We could use instantiate_vars
-- instead.
meta def open_n_pis : ℕ → expr → tactic (list expr × expr)
| 0       e := pure ([], e)
| (n + 1) e := do
  ⟨cnst, e⟩ ← open_pi e,
  ⟨args, u⟩ ← open_n_pis n e,
  pure $ (cnst :: args, u)

meta def get_n_pis_aux : ℕ → expr → list expr → tactic (list expr)
| 0 e acc := pure acc
| (n + 1) (pi pp_name binfo type e) acc := do
  let type := type.instantiate_vars acc,
  c ← mk_local' pp_name binfo type,
  get_n_pis_aux n e (acc ++ [c])
| _ e _ := fail! "expected an expression starting with a pi, but got\n{e}"

meta def get_n_pis (n : ℕ) (e : expr) : tactic (list expr) :=
get_n_pis_aux n e []

/--
For an input expression `e = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U`,
`open_pis_normalizing e` returns the following:

- For each `xᵢ`: the name `xᵢ`; a fresh local constant `cᵢ` which
  replaces `xᵢ` in the other returned expressions; and whether `xᵢ` is a
  dependent argument (i.e. whether it occurs in the remainder of `e`).
  The type `Tᵢ` is the type of `cᵢ`.
- The return type `U`.
-/
-- TODO doc
-- TODO could be more efficient: open_binder uses instantiate_var once per
-- binder, so the expression is traversed a lot. We could use instantiate_vars
-- instead.
meta def open_pis_normalizing
  : expr → tactic (list (expr × bool) × expr) := λ e, do
  e ← whnf e,
  match e with
  | (pi _ _ _ rest) := do
    -- TODO the next line makes this function quadratic in the size of the
    -- expression.
    let dep := rest.has_var_idx 0,
    ⟨cnst, e⟩ ← open_pi e,
    ⟨args, u⟩ ← open_pis_normalizing e,
    pure $ ⟨(cnst, dep) :: args, u⟩
  | _ := pure ⟨[], e⟩
  end

meta def get_app_fn_const_normalizing : expr → tactic name := λ e, do
  e ← whnf e,
  match e with
  | (const n _) := pure n
  | (app f _) := get_app_fn_const_normalizing f
  | _ := fail! "expected a constant (possibly applied to some arguments), but got:\n{e}"
  end

meta def get_inductive_name (type : expr) : tactic name := do
  n ← get_app_fn_const_normalizing type,
  env ← get_env,
  guard (env.is_inductive n) <|> fail! "Expected {n} to be an inductive type.",
  pure n

/--
`fuzzy_type_match t s` is true iff `t` and `s` are definitionally equal.
-/
-- TODO is it worth extending this check to be more permissive? E.g. if a
-- constructor argument has type `list α` and the index has type `list β`, we
-- may want to consider these types sufficiently similar to inherit the name.
-- Same (but even more obvious) with `vec α n` and `vec α (n + 1)`.
meta def fuzzy_type_match (t s : expr) : tactic bool :=
  (is_def_eq t s *> pure tt) <|> pure ff
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
meta def decompose_constructor_type_return (num_params : ℕ) (args : expr_set)
  : expr → tactic (rb_multimap expr ℕ) := λ ret_type, do
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
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr)
  : bool :=
let base := arg_type.get_app_fn in
match base with
| (expr.const base _) := base = type_name
| _ := ff
end

@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)

@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(args : list constructor_argument_info)

@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/-- Gathers information about a constructor from the environment. Fails if `c`
does not refer to a constructor. -/
meta def get_constructor_info (env : environment) (num_params : ℕ) (c : name)
  : tactic constructor_info := do
  when (¬ env.is_constructor c) $ exceptional.fail format!
    "Expected {c} to be a constructor.",
  decl ← env.get c,
  args ← decompose_constructor_type num_params decl.type,
  pure
    { cname := decl.to_name,
      args := args.map_with_index $ λ i ⟨name, type, dep, index_occs⟩,
        ⟨name, type, dep, index_occs.to_list⟩,
    }

/-- Gathers information about an inductive type from the environment. Fails if
`T` does not refer to an inductive type. -/
meta def get_inductive_info (env : environment) (T : name)
  : tactic inductive_info := do
  when (¬ env.is_inductive T) $ exceptional.fail format!
    "Expected {T} to be an inductive type.",
  decl ← env.get T,
  let type := decl.type,
  let num_params := env.inductive_num_params T,
  let num_indices := env.inductive_num_indices T,
  let constructor_names := env.constructors_of T,
  constructors ← constructor_names.mmap
    (get_constructor_info env num_params),
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

meta def get_eliminee_info (ename : name) : tactic eliminee_info := do
  e ← get_local ename,
  type ← infer_type e,
  ⟨f, args⟩ ← type.decompose_app_normalizing,
  pure
    { ename := ename,
      eexpr := e,
      type := type,
      args := args.to_rb_map }

meta structure constructor_argument_naming_info :=
(einfo : eliminee_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → tactic (list name)

meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule := λ i,
if is_recursive_constructor_argument i.iinfo.iname i.ainfo.type
  then pure [i.einfo.ename]
  else failed

meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule := λ i,
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

meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule := λ i,
let arg_name := i.ainfo.aname in
let arg_dep := i.ainfo.dependent in
if ! arg_dep && arg_name.is_likely_generated_name
  then failed
  else pure [arg_name]

meta def constructor_argument_naming_rule_type : constructor_argument_naming_rule := λ i, do
typical_variable_names i.ainfo.type

meta def default_constructor_argument_name : name := `x

meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule)
  : tactic (list name) :=
  first (rules.map ($ info)) <|> pure [default_constructor_argument_name]

meta def constructor_argument_names (info : constructor_argument_naming_info)
  : tactic (list name) :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named
  , constructor_argument_naming_rule_type ]

-- TODO this only works with simple names
meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

-- TODO the implementation is a bit of an 'orrible hack
meta def get_unused_name'_aux (n : name) (reserved : name_set)
  : option nat → tactic name := λ suffix, do
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

/- Precond: ns is nonempty. -/
meta def get_unused_name' (ns : list name) (reserved : name_set) : tactic name := do
  let fallback := ns.head,
  let ns := ns.filter (λ n, ¬ reserved.contains n),
  n ← try_core $ first $ ns.map $ λ n, do {
    guard (¬ reserved.contains n),
    fail_if_success (resolve_name n),
    pure n
  },
  match n with
  | some n := pure n
  | none := get_unused_name'_aux fallback reserved none
  end

/- Precond: ns is nonempty. -/
meta def intro_fresh (ns : list name) (reserved : name_set) : tactic expr := do
  n ← get_unused_name' ns reserved,
  intro n

inductive intro_spec
| as_is (n : name)
| fresh (ns : list name) -- ns must be nonempty

/- Precond: each of the name lists is nonempty. -/
meta def intro_lst_fresh (ns : list intro_spec) (reserved : name_set)
  : tactic (list expr) := do
ns.mmap $ λ spec,
  match spec with
  | intro_spec.as_is n := intro n
  | intro_spec.fresh ns := intro_fresh ns reserved
  end

-- TODO integrate into tactic.rename?
-- Precond: each of the name lists in `renames` must be nonempty.
meta def rename_fresh (renames : name_map (list name)) (reserved : name_set)
  : tactic (name_map name) := do
  ctx ← revertible_local_context,
  let ctx_suffix := ctx.drop_while (λ h, (renames.find h.local_pp_name).is_none),
  let new_names :=
    ctx_suffix.map $ λ h,
      match renames.find h.local_pp_name with
      | none := intro_spec.as_is h.local_pp_name
      | some new_names := intro_spec.fresh new_names
      end,
  revert_lst ctx_suffix,
  new_hyps ← intro_lst_fresh new_names reserved,
  pure $ rb_map.of_list $
    list.map₂ (λ (old new : expr), (old.local_pp_name, new.local_pp_name))
      ctx_suffix new_hyps

meta def type_depends_on_locals (h : expr) (ns : name_set) : tactic bool := do
  h_type ← infer_type h,
  pure $ h_type.has_local_in ns

meta def local_def_depends_on_locals (h : expr) (ns : name_set) : tactic bool := do
  (some h_val) ← try_core $ local_def_value h | pure ff,
  pure $ h_val.has_local_in ns

/- Precond: h is a local constant. -/
meta def local_depends_on_locals (h : expr) (ns : name_set) : tactic bool :=
list.mbor
  [ pure $ ns.contains h.local_uniq_name
  , type_depends_on_locals h ns
  , local_def_depends_on_locals h ns
  ]

meta def local_dependencies_of_local (h : expr) : tactic name_set := do
  let deps := mk_name_set.insert h.local_uniq_name,
  t ← infer_type h,
  let deps := deps.merge t.local_unique_names,
  (some val) ← try_core $ local_def_value h | pure deps,
  let deps := deps.merge val.local_unique_names,
  pure deps

meta def revert_lst'' (hs : name_set) : tactic (ℕ × list expr) := do
  ctx ← revertible_local_context,
  -- We take the 'dependency closure' of hs: any hypothesis that depends on any
  -- of the hypotheses in hs should get reverted. revert_lst can do this for us,
  -- but it doesn't report which hypotheses were actually reverted (only how
  -- many).
  to_revert ← ctx.mfilter_map $ λ h, do {
    dep_on_reverted ← local_depends_on_locals h hs,
    pure $ if dep_on_reverted then some h else none
  },
  num_reverted ← revert_lst to_revert,
  pure (num_reverted, to_revert)

meta def revert_lst' (hs : list expr) : tactic (ℕ × list expr) :=
revert_lst'' $ name_set.of_list $ hs.map expr.local_uniq_name

-- precond: fixed contains only locals
meta def generalize_hyps (eliminee : expr) (fixed : list expr) : tactic (ℕ × list expr) := do
  tgt ← target,
  let tgt_dependencies := tgt.local_unique_names,
  eliminee_type ← infer_type eliminee,
  eliminee_dependencies ← local_dependencies_of_local eliminee,
  fixed_dependencies ←
    name_set.merge_many <$> (eliminee :: fixed).mmap local_dependencies_of_local,
  ctx ← revertible_local_context,
  to_revert ← ctx.mfilter_map $ λ h, do {
    h_type ← infer_type h,
    let h_name := h.local_uniq_name,
    let rev :=
      ¬ fixed_dependencies.contains h_name ∧
      (tgt_dependencies.contains h_name ∨ h_type.has_local_in eliminee_dependencies),
    -- TODO I think `h_type.has_local_in eliminee_dependencies` is an
    -- overapproximation. What we actually want is any hyp that depends either
    -- on the eliminee or on one of the eliminee's index args. (But the
    -- overapproximation seems to work okay in practice as well.)
    pure $ if rev then some h_name else none
  },
  revert_lst'' $ name_set.of_list to_revert

meta def intron_fresh : ℕ → tactic (list expr)
| 0 := pure []
| (n + 1) := do
  nam ← mk_fresh_name,
  h ← intro nam,
  hs ← intron_fresh n,
  pure $ h :: hs

meta def constructor_intros (generate_induction_hyps : bool)
  (iinfo : inductive_info) (cinfo : constructor_info)
  : tactic (list (name × constructor_argument_info) × list (name × name)) := do
  let args := cinfo.args.drop iinfo.num_params,
  let num_args := args.length,
  arg_hyps ← intron_fresh num_args,
  let arg_hyp_names :=
    list.map₂ (λ (h : expr) ainfo, (h.local_pp_name, ainfo)) arg_hyps args,
  tt ← pure generate_induction_hyps | pure (arg_hyp_names, []),

  let rec_args := arg_hyp_names.filter $ λ x,
    is_recursive_constructor_argument iinfo.iname x.2.type,
    -- TODO the information whether an arg is recursive should be in
    -- constructor_argument_info.
  let num_ihs := rec_args.length,
  ih_hyps ← intron_fresh num_ihs,
  let ih_hyp_names :=
    list.map₂
      (λ (h : expr) (arg : name × constructor_argument_info),
        (h.local_pp_name, arg.1))
      ih_hyps rec_args,
  pure (arg_hyp_names, ih_hyp_names)

meta def constructor_renames (generate_induction_hyps : bool)
  (einfo : eliminee_info) (iinfo : inductive_info) (cinfo : constructor_info)
  (args : list (name × constructor_argument_info)) (ihs : list (name × name))
  : tactic (list expr × list expr) := do
  -- Rename constructor arguments
  let iname := iinfo.iname,
  arg_renames : list (name × list name) ←
    args.mmap $ λ ⟨old, ainfo⟩, do {
      new ← constructor_argument_names ⟨einfo, iinfo, cinfo, ainfo⟩,
      pure (old, new)
    },
  let arg_renames := rb_map.of_list arg_renames,
  new_arg_names ← rename_fresh arg_renames mk_name_set,
  new_arg_hyps ← args.mfilter_map $ λ ⟨a, _⟩, do {
    (some new_name) ← pure $ new_arg_names.find a | pure none,
    some <$> get_local new_name
  },

  -- Rename induction hypotheses (if we generated them)
  tt ← pure generate_induction_hyps | pure (new_arg_hyps, []),
  ih_renames ← ihs.mmap $ λ ⟨ih_hyp, arg_hyp⟩, do {
    some arg_hyp ← pure $ new_arg_names.find arg_hyp,
    pure $ (ih_hyp, ih_name arg_hyp)
  },
  let ih_renames : list (name × list name) :=
    match ih_renames with
    | [] := []
    | [(h, n)] := [(h, ["ih", n])]
    | ns := ns.map (λ ⟨h, n⟩, (h, [n]))
    end,
  new_ih_names ← rename_fresh (rb_map.of_list ih_renames) mk_name_set,
  new_ih_hyps ← ihs.mfilter_map $ λ ⟨a, _⟩, do {
    (some new_name) ← pure $ new_ih_names.find a | pure none,
    some <$> get_local new_name
  },
  pure (new_arg_hyps, new_ih_hyps)

meta def match_structure_equation (t : expr)
  : tactic (option (list level × list expr × list name × level × expr × expr × expr)) :=
try_core $ do
  ⟨u, type, lhs, rhs⟩ ← t.match_eq,
  ⟨const struct struct_levels, params⟩ ← decompose_app_normalizing type,
  env ← get_env,
  fields ← env.structure_fields struct,
  let fields := fields.map (λ n, struct ++ n),
  [constructor] ← pure $ env.constructors_of struct,
  c ← get_app_fn_const_normalizing rhs,
  guard $ c = constructor,
  pure (struct_levels, params, fields, u, type, lhs, rhs)

meta def decompose_structure_equation_once (h : expr)
  (struct_levels : list level) (params : list expr) (fields : list name)
  (u : level) (type lhs rhs : expr)
  : tactic (list (expr × expr)) :=
fields.mmap (λ f, do
    let proj := (const f struct_levels).mk_app params,
    let lhs' := proj lhs,
    let rhs' := proj rhs,
    rhs' ← unfold_proj rhs',
    lhs'_type ← infer_type lhs',
    rhs'_type ← infer_type rhs',
    sort u' ← infer_type lhs'_type,
    type_eq ← succeeds $ is_def_eq lhs'_type rhs'_type,
    if type_eq
      then do
        let eq_type := (const `eq [u]) lhs'_type lhs' rhs',
        let eq_prf := (const `congr_arg [u, u']) type lhs'_type lhs rhs proj h,
        pure (eq_prf, eq_type)
      else do
        let eq_type := (const `heq [u]) lhs'_type lhs' rhs'_type rhs',
        eq_prf ← to_expr ``(@congr_arg_heq %%type _ %%proj %%lhs %%rhs %%h) ff,
        instantiate_mvars eq_prf,
        pure (eq_prf, eq_type)
  )

meta def decompose_structure_equation
  : expr → expr → tactic (list (expr × expr) × name_set) :=
λ e e_type, do
  some ⟨struct_levels, params, fields, u, type, lhs, rhs⟩ ←
    match_structure_equation e_type
    | pure ([(e, e_type)], mk_name_set),
  children ←
    decompose_structure_equation_once e struct_levels params fields u type lhs rhs,
  child_results
    ← children.mmap (λ ⟨e, e_type⟩, decompose_structure_equation e e_type),
  let child_equations := (child_results.map prod.fst).join,
  let child_fields := name_set.merge_many (child_results.map prod.snd),
  pure (child_equations, child_fields)

meta def decompose_structure_equation_hyp (h : expr) : tactic name_set := do
  h_type ← infer_type h,
  some _ ← match_structure_equation h_type | pure mk_name_set,
  ⟨hs, fields⟩ ← decompose_structure_equation h h_type,
  hs.mmap' $ λ ⟨i, i_type⟩, do {
    n ← mk_fresh_name,
    h ← assertv n i_type i,
    subst_core h <|> clear h
    -- TODO we can check more specifically whether h has the right shape
    -- for substitution
  },
  pure fields

namespace interactive

open interactive
open lean.parser

meta def decompose_structure_equation (h : parse ident) : tactic unit := do
  h ← get_local h,
  decompose_structure_equation_hyp h,
  pure ()

end interactive

meta def generalize_complex_index_args (eliminee : expr) (index_args : list expr)
  : tactic (expr × ℕ × list name × name_set) := do
  let ⟨locals, nonlocals⟩ :=
    index_args.partition (λ arg : expr, arg.is_local_constant),

  -- If there aren't any complex index arguments, we don't need to do anything.
  (_ :: _) ← pure nonlocals | pure (eliminee, 0, [], mk_name_set),

  -- Revert the eliminee (and any hypotheses depending on it).
  num_reverted_eliminee ← revert eliminee,

  -- Revert any hypotheses depending on one of the complex index arguments
  (num_reverted_args : ℕ) ← list.sum <$> nonlocals.mmap revert_kdependencies,
  -- TODO is revert_kdependencies broken with local defs?

  -- Generate fresh names for the index variables and equations
  generalizes_args ← nonlocals.mmap $ λ arg, do {
    -- TODO better names?
    pure (`index, some `index_eq, arg)
  },

  -- Generalise the complex index arguments
  index_vars_eqs ← generalizes_intro generalizes_args,

  -- Every second hypothesis introduced by `generalizes` is an index equation.
  -- The other introduced hypotheses are the index variables.
  let ⟨index_vars, index_equations⟩ :=
    @list.foldr_with_index expr (list name × list name)
      (λ i (h : expr) ⟨vars, eqs⟩,
        let n := h.local_pp_name in
        if i % 2 = 0 then (n :: vars, eqs) else (vars, n :: eqs))
      ([], [])
      index_vars_eqs,

  -- Decompose the index equations equating elements of structures.
  -- Note: Each step in the following loop may change the unique names of
  -- hypotheses in the context, so we go by pretty names. `generalizes_intro`
  -- and decompose_structure_equation_hyp make sure that these are unique.
  fields ← index_equations.mmap $ λ eq, do {
    eq ← get_local eq,
    decompose_structure_equation_hyp eq
  },
  let fields := name_set.merge_many fields,

  -- Re-introduce the indices' dependencies
  intron num_reverted_args,

  -- Re-introduce the eliminee and its dependencies
  intron (num_reverted_eliminee - 1),
  eliminee ← intro1,

  -- Re-revert the index equations
  index_var_equations ← index_equations.mmap get_local,
  revert_lst index_var_equations,

  pure (eliminee, nonlocals.length, index_vars, fields)

meta def replace' (h : expr) (x : expr) (t : option expr := none) : tactic expr := do
  h' ← note h.local_pp_name t x,
  clear h,
  pure h'

meta inductive simplification_result
| simplified (next_equations : list name)
| not_simplified
| goal_solved

open simplification_result

meta def simplify_heterogeneous_index_equation (equ lhs_type rhs_type lhs rhs : expr)
  : tactic simplification_result :=
do {
  is_def_eq lhs_type rhs_type,
  p ← to_expr ``(@eq_of_heq %%lhs_type %%lhs %%rhs %%equ),
  t ← to_expr ``(@eq %%lhs_type %%lhs %%rhs),
  equ ← replace' equ p (some t),
  pure $ simplified [equ.local_pp_name]
} <|>
pure not_simplified

meta def simplify_defeq_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  is_def_eq lhs rhs,
  clear equ,
  pure $ simplified []
} <|>
pure not_simplified

meta def simplify_var_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  guard $ lhs.is_local_constant ∨ rhs.is_local_constant,
  subst equ,
  pure $ simplified []
} <|>
pure not_simplified

meta def get_sizeof (type : expr) : tactic (name × pexpr) := do
  n ← get_inductive_name type,
  let sizeof_name := n ++ `sizeof,
  sizeof_const ← resolve_name $ sizeof_name,
  pure (sizeof_name, sizeof_const)

meta def simplify_cyclic_equation_aux (equ type lhs rhs : expr) : tactic unit :=
solve1 $ do
  (sizeof_name, sizeof) ← get_sizeof type,
  hyp_type ← to_expr ``(@eq ℕ (%%sizeof %%lhs) (%%sizeof %%rhs)),
  hyp_body ← to_expr ``(@congr_arg %%type ℕ %%lhs %%rhs %%sizeof %%equ),
  hyp_name ← mk_fresh_name,
  h ← note hyp_name hyp_type hyp_body,
  interactive.simp none tt [simp_arg_type.expr sizeof] []
    (interactive.loc.ns [hyp_name]),
  `[linarith]
  -- TODO the blanket 'linarith' here is a bit heavy. We could probably use
  -- something more targeted.

meta def simplify_cyclic_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  simplify_cyclic_equation_aux equ type lhs rhs <|> do {
    equ_symm ← to_expr ``(eq.symm %%equ),
    simplify_cyclic_equation_aux equ_symm type rhs lhs
  },
  pure goal_solved
} <|>
pure not_simplified

meta def dedup_single (hyp : expr) : tactic expr := do
  ctx ← local_context,
  let old_name := hyp.local_pp_name,
  let dup := ctx.any (λ h, h ≠ hyp ∧ h.local_pp_name = old_name),
  tt ← pure dup | pure hyp,
  new_name ← get_unused_name old_name,
  n ← revert_after hyp,
  revert hyp,
  hyp ← intro new_name,
  intron n,
  pure hyp

meta def decompose_and : expr → tactic (list expr) := λ h, do
  t ← infer_type h,
  match t with
  | `(%%P ∧ %%Q) := do
    h₁ ← to_expr ``(@and.elim_left %%P %%Q %%h),
    h₂ ← to_expr ``(@and.elim_right %%P %%Q %%h),
    let h_name := h.local_pp_name,
    h₁ ← note h_name P h₁,
    h₂ ← note h_name Q h₂,
    clear h,
    h₂ ← dedup_single h₂,
    h₁ ← dedup_single h₁,
    hs₁ ← decompose_and h₁,
    hs₂ ← decompose_and h₂,
    pure $ hs₁ ++ hs₂
  | _ := pure [h]
  end

meta def simplify_constructor_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
do {
  (const f _, lhs_args) ← decompose_app_normalizing lhs,
  (const g _, rhs_args) ← decompose_app_normalizing rhs,
  env ← get_env,
  guard $ env.is_constructor f,
  guard $ env.is_constructor g,
  if f ≠ g
    then do
      solve1 $ cases equ,
      pure goal_solved
    else do
      inj ← resolve_name (f ++ "inj"),
      p ← to_expr ``(%%inj %%equ),
      equ ← replace' equ p,
      equs ← decompose_and equ,
      pure $ simplified $ equs.map (λ h, h.local_pp_name)
} <|>
pure not_simplified

meta def sequence_simplifiers (s t : tactic simplification_result)
  : tactic simplification_result := do
  r ← s,
  match r with
  | simplified _ := pure r
  | goal_solved := pure r
  | not_simplified := t
  end

meta def simplify_homogeneous_index_equation (equ type lhs rhs : expr)
  : tactic simplification_result :=
  list.foldl sequence_simplifiers (pure not_simplified)
    [ simplify_defeq_equation equ type lhs rhs
    , simplify_var_equation equ type lhs rhs
    , simplify_constructor_equation equ type lhs rhs
    , simplify_cyclic_equation equ type lhs rhs
    ]

meta def simplify_index_equation_once (equ : name) : tactic simplification_result := do
  equ ← get_local equ,
  t ← infer_type equ,
  match t with
  | `(@eq %%type %%lhs %%rhs) :=
    simplify_homogeneous_index_equation equ type lhs rhs
  | `(@heq %%lhs_type %%lhs %%rhs_type %%rhs) := do
    simplify_heterogeneous_index_equation equ lhs_type rhs_type lhs rhs
  | _ := fail! "Expected {equ} to be an equation, but its type is\n{t}."
  end

meta def simplify_index_equations : list name → tactic bool
| [] := pure ff
| (h :: hs) := do
  res ← simplify_index_equation_once h,
  match res with
  | simplified hs' := simplify_index_equations $ hs' ++ hs
  | not_simplified := simplify_index_equations hs
  | goal_solved := pure tt
  end

namespace interactive

open lean.parser

meta def simplify_index_equations (eqs : interactive.parse (many ident))
  : tactic unit :=
tactic.simplify_index_equations eqs *> skip

end interactive

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

meta def ih_apps (num_equations : ℕ) (ih : expr) (ih_type : expr)
  : tactic (expr × list expr) :=
ih_apps_aux ih [] num_equations ih_type

meta def assign_unassigned_mvar (mv : expr) (pp_name : name)
  (binfo : binder_info) : tactic (option expr) := do
  ff ← is_assigned mv | pure none,
  type ← infer_type mv,
  c ← mk_local' pp_name binfo type,
  unify mv c,
  pure c

meta def assign_unassigned_mvars (mvars : list (expr × name × binder_info))
  : tactic (list expr) :=
mvars.mfilter_map $ λ ⟨mv, pp_name, binfo⟩,
  assign_unassigned_mvar mv pp_name binfo

meta def simplify_ih (num_generalized : ℕ) (num_index_vars : ℕ) (ih : expr)
  : tactic expr := do
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
private meta def hyp_unique_names : tactic name_set :=
do ctx ← local_context,
   pure $ ctx.foldl (λ r h, r.insert h.local_uniq_name) mk_name_set

/--
Returns all hypotheses (local constants) from the context except those whose
unique names are in `hyp_uids`.
-/
-- TODO copied from init.meta.interactive
private meta def hyps_except (hyp_uids : name_set) : tactic (list expr) :=
do ctx ← local_context,
   pure $ ctx.filter (λ (h : expr), ¬ hyp_uids.contains h.local_uniq_name)

/--
  Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
-- TODO copied from init.meta.interactive
private meta def set_cases_tags (in_tag : tag) (rs : list (name × list expr)) : tactic unit :=
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

meta def unfold_only (to_unfold : list name) (e : expr) (fail_if_unchanged := tt)
  : tactic expr :=
simp_lemmas.dsimplify simp_lemmas.mk to_unfold e
  { eta := ff, zeta := ff, beta := ff, iota := ff
  , fail_if_unchanged := fail_if_unchanged }

meta def unfold_only_target (to_unfold : list name) (fail_if_unchanged := tt)
  : tactic unit := do
  tgt ← target,
  tgt ← unfold_only to_unfold tgt fail_if_unchanged,
  unsafe_change tgt

-- Note: frozen local instances.
-- Note: changes all unique names.
meta def unfold_only_everywhere (to_unfold : list name) (fail_if_unchanged := tt)
  : tactic unit := do
  n ← revert_all,
  unfold_only_target to_unfold fail_if_unchanged,
  intron n

meta def revert_all_except (hyp_unique_names : name_set) : tactic ℕ := do
  ctx ← revertible_local_context,
  let ctx := ctx.filter (λ h, ¬ hyp_unique_names.contains h.local_uniq_name),
  revert_lst ctx

meta def eliminate (eliminee_name : name) (generate_induction_hyps : bool)
  (fixed : list name := []) : tactic unit :=
focus1 $ do
  einfo ← get_eliminee_info eliminee_name,
  let eliminee := einfo.eexpr,
  let eliminee_type := einfo.type,
  let eliminee_args := einfo.args.values.reverse,
  env ← get_env,

  -- Get info about the inductive type
  iname ← get_inductive_name eliminee_type <|> fail!
    "The type of {eliminee_name} should be an inductive type, but it is\n{eliminee_type}",
  iinfo ← get_inductive_info env iname,

  -- TODO We would like to disallow mutual/nested inductive types, since these
  -- have complicated recursors which we probably don't support. However, there
  -- seems to be no way to find out whether an inductive type is mutual/nested.
  -- (`environment.is_ginductive` doesn't seem to work.)

  -- Generalise complex indices
  (eliminee, num_index_vars, index_var_names, structure_field_names) ←
    generalize_complex_index_args eliminee (eliminee_args.drop iinfo.num_params),

  -- Generalise all generalisable hypotheses except those mentioned in a "fixing"
  -- clause.
  -- TODO This is only needed in 'induction' mode, though it doesn't do any harm
  -- in 'cases' mode.
  fix_exprs ← fixed.mmap get_local,
  ⟨num_generalized, generalized_hyps⟩ ←
    generalize_hyps eliminee fix_exprs,
  let generalized_names :=
    name_set.of_list $ generalized_hyps.map expr.local_pp_name,

  -- NOTE: The previous step may have changed the unique names of all hyps in
  -- the context.

  -- Record the current case tag and the unique names of all hypotheses in the
  -- context.
  in_tag ← get_main_tag,
  old_hyps ← hyp_unique_names,

  -- Apply the recursor. We first try the nondependent recursor, then the
  -- dependent recursor (if available).
  let rec_suffix := if generate_induction_hyps then "rec_on" else "cases_on",
  let drec_suffix := if generate_induction_hyps then "drec_on" else "dcases_on",
  rec ← mk_const $ iname ++ rec_suffix,
  drec ← try_core $ mk_const $ iname ++ drec_suffix,
  interactive.apply ``(%%rec %%eliminee)
    <|> (do drec ← drec, interactive.apply ``(%%drec %%eliminee))
    <|> fail! "Failed to apply the (dependent) recursor for {iname}.",

  -- For each case (constructor):
  cases : list (option (name × list expr)) ←
    focus $ iinfo.constructors.map $ λ cinfo, do {
      -- Get the eliminee's arguments. (Some of these may have changed due to
      -- the generalising step above.)
      -- TODO propagate this information instead of re-parsing the type here?
      eliminee_type ← infer_type eliminee,
      ⟨_, eliminee_args⟩ ← decompose_app_normalizing eliminee_type,

      -- Clear the eliminated hypothesis (if possible)
      try $ clear eliminee,

      -- Clear the index args (unless other stuff in the goal depends on them)
      -- TODO is this the right thing to do? I don't think this necessarily
      -- preserves provability: The args we clear could contain interesting
      -- information, even if nothing else depends on them. Is there a way to
      -- avoid this, i.e. clean up even more conservatively?
      eliminee_args.mmap' (try ∘ clear),

      -- Unfold structure projections which may have been introduced by the
      -- structure equation simplification step of generalize_complex_index_args.
      -- TODO This method reduces every occurrence of the given structure field
      -- projections, not only those which we actually introduced. This may
      -- yield some surprising results, but I don't see an easy way to prevent
      -- it.
      n ← revert_all_except old_hyps,
      unfold_only_target structure_field_names.to_list ff,
      intron n,

      -- NOTE: The previous step invalidates all unique names (except those of
      -- the old hyps).

      -- Introduce the constructor arguments
      (constructor_arg_names, ih_names) ←
        constructor_intros generate_induction_hyps iinfo cinfo,

      -- Introduce any hypotheses we've previously generalised
      generalized_hyps ← intron' num_generalized,

      -- Introduce the index equations
      index_equations ← intron' num_index_vars,

      -- Simplify the index equations. Stop after this step if the goal has been
      -- solved by the simplification.
      ff ← simplify_index_equations (index_equations.map expr.local_pp_name)
        | pure none,

      -- Simplify the induction hypotheses
      -- NOTE: The previous step may have changed the unique names of the
      -- induction hypotheses, so we have to locate them again. Their pretty
      -- names should be unique in the context, so we can use these.
      (ih_names.map prod.fst).mmap'
        (get_local >=> simplify_ih num_generalized num_index_vars),

      -- Try to clear the index variables. These often become unused during
      -- the index equation simplification step.
      index_var_names.mmap $ λ h, try (get_local h >>= clear),

      -- Rename the constructor names and IHs. We do this here (rather than
      -- earlier, when we introduced them) because there may now be less
      -- hypotheses in the context, and therefore more of the desired
      -- names may be free.
      ⟨constructor_arg_hyps, ih_hyps⟩ ←
        constructor_renames generate_induction_hyps einfo iinfo cinfo
          constructor_arg_names ih_names,

      -- Return the constructor name and the renamable new hypotheses. These are
      -- the hypotheses that can later be renamed by the `case` tactic. Note
      -- that index variables and index equations are not renamable. This may be
      -- counterintuitive in some cases, but it's surprisingly difficult to
      -- catch exactly the relevant hyps here.
      pure $ some (cinfo.cname, constructor_arg_hyps ++ ih_hyps)
    },

  set_cases_tags in_tag (cases.filter_map id),

  pure ()

end tactic


namespace tactic.interactive

open interactive lean.parser

precedence `fixing`:0

meta def induction' (hyp : parse ident)
  (fixed : parse (optional (tk "fixing" *> many ident))) : tactic unit :=
tactic.eliminate hyp tt (fixed.get_or_else [])

meta def cases' (hyp : parse ident) : tactic unit :=
tactic.eliminate hyp ff []

end tactic.interactive

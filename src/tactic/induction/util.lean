/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import data.sum
import tactic.core
import data.buffer.parser

universes u v w


namespace list

open native

variables {α : Type u} {β : Type v}

def to_rbmap : list α → rbmap ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) (mk_rbmap ℕ α)

meta def to_rb_map {α : Type} : list α → rb_map ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) mk_rb_map

def all_some : list (option α) → option (list α)
| [] := some []
| (some x :: xs) := (λ xs, x :: xs) <$> all_some xs
| (none :: xs) := none

def take_lst {α} : list α → list ℕ → list (list α) × list α
| xs [] := ([], xs)
| xs (n :: ns) :=
  let ⟨xs₁, xs₂⟩ := xs.split_at n in
  let ⟨xss, rest⟩ := take_lst xs₂ ns in
  (xs₁ :: xss, rest)

def map₂_left' {α β γ} (f : α → option β → γ) : list α → list β → (list γ × list β)
| [] bs := ([], bs)
| (a :: as) [] :=
  let ⟨cs, rest⟩ := map₂_left' as [] in
  (f a none :: cs, rest)
| (a :: as) (b :: bs) :=
  let ⟨cs, rest⟩ := map₂_left' as bs in
  (f a (some b) :: cs, rest)

def map₂_right' {α β γ} (f : option α → β → γ) (as : list α) (bs : list β) :
  (list γ × list α) :=
map₂_left' (flip f) bs as

def zip_left' {α β} : list α → list β → list (α × option β) × list β :=
map₂_left' (λ a b, (a, b))

def zip_right' {α β} : list α → list β → list (option α × β) × list α :=
map₂_right' (λ a b, (a, b))

def map₂_left {α β γ} (f : α → option β → γ) : list α → list β → list γ
| [] _ := []
| (a :: as) [] := f a none :: map₂_left as []
| (a :: as) (b :: bs) := f a (some b) :: map₂_left as bs

def map₂_right {α β γ} (f : option α → β → γ) (as : list α) (bs : list β) :
  list γ :=
map₂_left (flip f) bs as

def zip_left {α β} : list α → list β → list (α × option β) :=
map₂_left prod.mk

def zip_right {α β} : list α → list β → list (option α × β) :=
map₂_right prod.mk

lemma map₂_left_eq_map₂_left' {α β γ} (f : α → option β → γ)
  : ∀ (as : list α) (bs : list β),
    map₂_left f as bs = (map₂_left' f as bs).fst
| [] bs := by simp!
| (a :: as) [] := by { simp! only [*], cases (map₂_left' f as nil), simp!  }
| (a :: as) (b :: bs) := by { simp! only [*], cases (map₂_left' f as bs), simp! }

def fill_nones {α} : list (option α) → list α → list α
| [] _ := []
| ((some a) :: as) as' := a :: fill_nones as as'
| (none :: as) [] := as.reduce_option
| (none :: as) (a :: as') := a :: fill_nones as as'

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

variables [has_lt α] [decidable_rel ((<) : α → α → Prop)]

meta def find (m : rb_multimap α β) (a : α) : option (rb_set β) :=
rb_map.find m a

variables [has_lt β] [decidable_rel ((<) : β → β → Prop)]

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

meta def to_list' (m : rb_multimap α β) : list (α × list β) :=
(rb_map.to_list m).map (λ ⟨a, bs⟩, ⟨a, bs.to_list⟩)

end rb_multimap

end native


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
meta def decompose_pi : expr →
  list (name × binder_info × expr × bool) × ℕ × expr
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
meta def decompose_pi_normalizing : expr →
  tactic (list (name × binder_info × expr × bool) × expr) :=
λ e, do
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

meta def recompose_pi (binders : list (name × binder_info × expr)) (ret : expr) :
  expr :=
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
meta def decompose_app_normalizing (e : expr) (md := semireducible) :
  tactic (expr × list expr) := do
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


namespace name

open parser

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

open expr

meta def open_pis_whnf_dep :
  expr → tactic (list (expr × bool) × expr) := λ e, do
  e' ← whnf e,
  match e' with
  | (pi n bi t rest) := do
    c ← mk_local' n bi t,
    let dep := rest.has_var,
    (cs, rest) ← open_pis_whnf_dep $ rest.instantiate_var c,
    pure ((c, dep) :: cs, rest)
  | _ := pure ([], e)
  end

meta def open_n_pis_metas' :
  expr → ℕ → tactic (list (expr × name × binder_info) × expr)
| e 0 := pure ([], e)
| (pi nam bi t rest) (n + 1) := do
  m ← mk_meta_var t,
  (ms, rest) ← open_n_pis_metas' (rest.instantiate_var m) n,
  pure ((m, nam, bi) :: ms, rest)
| e (n + 1) := fail! "expected an expression starting with a Π, but got: {e}"


meta def get_app_fn_const_whnf (e : expr) : tactic name := do
  f ← get_app_fn_whnf e,
  f ← whnf f,
  match f with
  | (const n _) := pure n
  | _ := fail! "expected a constant (possibly applied to some arguments), but got:\n{e}"
  end

meta def get_inductive_name (type : expr) : tactic name := do
  n ← get_app_fn_const_whnf type,
  env ← get_env,
  guard (env.is_inductive n) <|> fail! "Expected {n} to be an inductive type.",
  pure n

meta def type_depends_on_locals (h : expr) (ns : name_set) : tactic bool := do
  h_type ← infer_type h,
  pure $ h_type.has_local_in ns

meta def local_def_depends_on_locals (h : expr) (ns : name_set) : tactic bool := do
  (some h_val) ← try_core $ local_def_value h | pure ff,
  pure $ h_val.has_local_in ns

/--
Test whether `h` depends on any of the hypotheses in the set of unique names
`ns`. This is the case if `h` is in `ns`, or if any of the `ns` appear in `h`'s
type or body.
-/
meta def local_depends_on_locals (h : expr) (ns : name_set) : tactic bool :=
list.mbor
  [ pure $ ns.contains h.local_uniq_name
  , type_depends_on_locals h ns
  , local_def_depends_on_locals h ns
  ]

meta def local_depends_on_local (h i : expr) : tactic bool :=
local_depends_on_locals h (mk_name_set.insert i.local_uniq_name)

/--
The set of unique names of hypotheses which `h` depends on (including `h`
itself). `h` must be a local constant.
-/
meta def dependencies_of_local (h : expr) : tactic name_set := do
  let deps := mk_name_set.insert h.local_uniq_name,
  t ← infer_type h,
  let deps := deps.union t.local_unique_names,
  (some val) ← try_core $ local_def_value h | pure deps,
  let deps := deps.union val.local_unique_names,
  pure deps

/--
The dependency closure of the local constants whose unique names appear in `hs`.
This is the set of local constants which depend on any of the `hs` (including
the `hs` themselves).
-/
meta def dependency_closure' (hs : name_set) : tactic (list expr) := do
  ctx ← local_context,
  ctx.mfilter $ λ h, local_depends_on_locals h hs

/--
The dependency closure of the local constants in `hs`. See `dependency_closure'`.
-/
meta def dependency_closure (hs : list expr) : tactic (list expr) :=
dependency_closure' $ name_set.of_list $ hs.map expr.local_uniq_name

/--
Revert the local constants whose unique names appear in `hs`, as well as any
hypotheses that depend on them. Returns the number of hypotheses that were
reverted and a list containing these hypotheses and their types.
-/
meta def revert_lst'' (hs : name_set) : tactic (ℕ × list (expr × expr)) := do
  to_revert ← dependency_closure' hs,
  to_revert_types ← to_revert.mmap infer_type,
  num_reverted ← revert_lst to_revert,
  pure (num_reverted, to_revert.zip to_revert_types)

/--
Revert the local constants in `hs`, as well as any hypotheses that depend on
them. See `revert_lst''`.
-/
meta def revert_lst' (hs : list expr) : tactic (ℕ × list (expr × expr)) :=
revert_lst'' $ name_set.of_list $ hs.map expr.local_uniq_name

end tactic

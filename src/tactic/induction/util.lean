/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.core
import data.buffer.parser

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

def mmap_with_index'_aux (f : ℕ → α → m punit) : ℕ → list α → m punit
| _ [] := pure ⟨⟩
| i (a :: as) := f i a *> mmap_with_index'_aux (i + 1) as

def mmap_with_index' (f : ℕ → α → m punit) (as : list α) : m punit :=
mmap_with_index'_aux f 0 as

end mmap_with_index

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


namespace rb_set

variables {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)]

meta def merge (xs ys : rb_set α) : rb_set α :=
ys.fold xs (λ a xs, xs.insert a)

meta def merge_many (xs : list (rb_set α)) : rb_set α :=
xs.foldl merge mk_rb_set

end rb_set

end native


namespace name_set

meta def merge (xs ys : name_set) : name_set :=
ys.fold xs (λ a xs, xs.insert a)

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


namespace sum

@[simp] def get_left {α β} : α ⊕ β → option α
| (inl a) := some a
| _ := none

@[simp] def get_right {α β} : α ⊕ β → option β
| (inr b) := some b
| _ := none

@[simp] def is_left {α β} : α ⊕ β → bool
| (inl _) := tt
| (inr _) := ff

@[simp] def is_right {α β} : α ⊕ β → bool
| (inl _) := ff
| (inr _) := tt

end sum


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
meta def open_pis_normalizing : expr →
  tactic (list (expr × bool) × expr) :=
λ e, do
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

meta def get_app_fn_const_normalizing : expr → tactic name :=
λ e, do
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
  let deps := deps.merge t.local_unique_names,
  (some val) ← try_core $ local_def_value h | pure deps,
  let deps := deps.merge val.local_unique_names,
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

meta def replace' (h : expr) (x : expr) (t : option expr := none) : tactic expr := do
  h' ← note h.local_pp_name t x,
  clear h,
  pure h'

end tactic

/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import data.sum
import tactic.core
import data.buffer.parser

universes u v w

open native tactic.interactive


namespace list

variables {α : Type u} {β : Type v}

def mfirst' {m : Type v → Type w} [monad m] (f : α → m (option β)) :
  list α → m (option β)
| [] := pure none
| (a :: as) := do
  (some b) ← f a | mfirst' as,
  pure (some b)

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

meta def mk_rb_multimap (α β) [has_lt α] [decidable_rel ((<) : α → α → Prop)] :
  rb_multimap α β :=
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

meta def locals (e : expr) : expr_set :=
e.fold mk_expr_set $ λ e _ occs,
  if e.is_local_constant then occs.insert e else occs

meta def local_unique_names (e : expr) : name_set :=
e.fold mk_name_set $ λ e _ occs,
  match e with
  | (local_const u _ _ _) := occs.insert u
  | _ := occs
  end

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


meta def get_app_fn_const_whnf (e : expr) (md := semireducible)
  (unfold_ginductive := tt) : tactic name := do
  f ← get_app_fn_whnf e md unfold_ginductive,
  match f with
  | (const n _) := pure n
  | _ := fail! "expected a constant (possibly applied to some arguments), but got:\n{e}"
  end

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
meta def revert_set (hs : name_set) : tactic (ℕ × list (expr × expr)) := do
  to_revert ← dependency_closure' hs,
  to_revert_with_types ← to_revert.mmap $ λ h, do {
    T ← infer_type h,
    pure (h, T)
  },
  num_reverted ← revert_lst to_revert,
  pure (num_reverted, to_revert_with_types)

/--
Revert the local constants in `hs`, as well as any hypotheses that depend on
them. See `revert_lst''`.
-/
meta def revert_lst' (hs : list expr) : tactic (ℕ × list (expr × expr)) :=
revert_set $ name_set.of_list $ hs.map expr.local_uniq_name

-- TODO the implementation is a bit of an 'orrible hack
private meta def get_unused_name_reserved_aux (n : name) (reserved : name_set) :
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
      get_unused_name_reserved_aux new_suffix

meta def get_unused_name_reserved (ns : list name) (reserved : name_set) :
  tactic name := do
  let fallback := match ns with | [] := `x | x :: _ := x end,
  (first $ ns.map $ λ n, do {
    guard (¬ reserved.contains n),
    fail_if_success (resolve_name n),
    pure n
  })
  <|>
  get_unused_name_reserved_aux fallback reserved none

/- Precond: ns is nonempty. -/
meta def intro_fresh_reserved (ns : list name) (reserved : name_set) : tactic expr :=
get_unused_name_reserved ns reserved >>= intro

/- Precond: each of the name lists is nonempty. -/
meta def intro_lst_fresh_reserved (ns : list (name ⊕ list name)) (reserved : name_set) :
  tactic (list expr) := do
  let fixed := name_set.of_list $ ns.filter_map sum.get_left,
  let reserved := reserved.union fixed,
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

end tactic

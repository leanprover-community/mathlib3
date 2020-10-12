/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import data.list.defs
import meta.expr
import tactic.core

/-!
# Tactics about dependencies

An expression `e` depends on another expression `f` if `f` occurs in `e` (see
note [dependencies of hypotheses] for details and corner cases). This module
provides tactics for checking whether hypotheses depend on each other and for
enumerating the dependencies and reverse dependencies of hypotheses.
-/

namespace tactic

/--
Given a hypothesis (local constant) `h` and a local constant `i`, we say that
`h` depends on `i` iff

- `i` appears in the type of `h` or
- `h` is a local definition and `i` appears in its body.

We say that `h` inclusively depends on `i` iff `h` depends on `i` or `h = i`
(so inclusive dependency is the reflexive closure of regular dependency).

For example, consider the following context:

```lean
P : ∀ n, fin n → Prop
n : ℕ
m : ℕ := n
f : fin m
h : P m f
```

Here, `m` depends on `n`; `f` depends on `m`; `h` depends on `P`, `m` and `f`.
Note that `f` and `h` do not depend on `n`, so the depends-on relation is not
transitive in the presence of local definitions. `h` inclusively depends on `h`,
`P`, `m` and `f`.

We also say that `m` is a dependency of `f` and `f` a reverse dependency of `m`.
Note that the Lean standard library sometimes uses these terms differently:
`kdependencies`, confusingly, computes the reverse dependencies of an
expression.
-/
library_note "dependencies of hypotheses"


/--
`type_has_local_in h ns` returns true iff the type of `h` contains a local
constant whose unique name appears in `ns`.
-/
meta def type_has_local_in (h : expr) (ns : name_set) : tactic bool := do
  h_type ← infer_type h,
  pure $ h_type.has_local_in ns

/--
`local_def_value_has_local_in h ns` returns true iff `h` is a local definition
whose body contains a local constant whose unique name appears in `ns`.
-/
meta def local_def_value_has_local_in (h : expr) (ns : name_set) : tactic bool := do
  (some h_val) ← try_core $ local_def_value h | pure ff,
  pure $ h_val.has_local_in ns

/--
Given a hypothesis `h`, `hyp_depends_on_locals h ns` returns true iff `h`
depends on a local constant whose unique name appears in `ns`. See note
[dependencies of hypotheses].
-/
meta def hyp_depends_on_locals (h : expr) (ns : name_set) : tactic bool :=
list.mbor
  [ type_has_local_in h ns,
    local_def_value_has_local_in h ns ]

/--
Given a hypothesis `h`, `hyp_depends_on_locals h ns` returns true iff `h`
inclusively depends on a local constant whose unique name appears in `ns`.
See note [dependencies of hypotheses].
-/
meta def hyp_depends_on_locals_inclusive (h : expr) (ns : name_set) : tactic bool :=
list.mbor
  [ pure $ ns.contains h.local_uniq_name,
    hyp_depends_on_locals h ns ]

/--
Given a hypothesis `h` and local constant `i`, `hyp_depends_on_local h i`
checks whether `h` depends on `i`. See note [dependencies of hypotheses].
-/
meta def hyp_depends_on_local (h i : expr) : tactic bool :=
hyp_depends_on_locals h (mk_name_set.insert i.local_uniq_name)

/--
Given a hypothesis `h` and local constant `i`, `hyp_depends_on_local h i`
checks whether `h` inclusively depends on `i`. See note
[dependencies of hypotheses].
-/
meta def hyp_depends_on_local_inclusive (h i : expr) : tactic bool :=
hyp_depends_on_locals_inclusive h (mk_name_set.insert i.local_uniq_name)

/--
Given a hypothesis `h`, `dependencies_of_hyp' h` returns the set of unique names
of the local constants which `h` depends on. See note
[dependencies of hypotheses].
-/
meta def dependencies_of_hyp' (h : expr) : tactic name_set := do
  t ← infer_type h,
  let deps := t.list_local_const_unique_names,
  (some val) ← try_core $ local_def_value h | pure deps,
  let deps := deps.union val.list_local_const_unique_names,
  pure deps

/--
Given a hypothesis `h`, `dependencies_of_hyp h` returns the hypotheses which `h`
depends on. See note [dependencies of hypotheses].
-/
meta def dependencies_of_hyp (h : expr) : tactic (list expr) := do
  ns ← dependencies_of_hyp' h,
  ns.to_list.mmap get_local

/--
Given a hypothesis `h`, `dependencies_of_hyp_inclusive' h` returns the set of
unique names of the local constants which `h` inclusively depends on. See note
[dependencies of hypotheses].
-/
meta def dependencies_of_hyp_inclusive' (h : expr) : tactic name_set := do
  deps ← dependencies_of_hyp' h,
  pure $ deps.insert h.local_uniq_name

/--
Given a hypothesis `h`, `dependencies_of_hyp_inclusive' h` returns the
hypotheses which `h` inclusively depends on. See note
[dependencies of hypotheses].
-/
meta def dependencies_of_hyp_inclusive (h : expr) : tactic (list expr) := do
  ns ← dependencies_of_hyp_inclusive' h,
  ns.to_list.mmap get_local

/--
Given a set `ns` of unique names of hypotheses,
`reverse_dependencies_of_hyps' hs` returns those hypotheses which depend on any
of the `hs`, excluding the `hs` themselves. See note
[dependencies of hypotheses].
-/
meta def reverse_dependencies_of_hyps' (hs : name_set) : tactic (list expr) := do
  ctx ← local_context,
  ctx.mfilter $ λ h, list.mband
    [ pure $ ¬ hs.contains h.local_uniq_name,
      hyp_depends_on_locals h hs ]

/--
`reverse_dependencies_of_hyps hs` returns those hypotheses which depend on any
of the hypotheses `hs`, excluding the `hs` themselves.
-/
meta def reverse_dependencies_of_hyps (hs : list expr) : tactic (list expr) :=
reverse_dependencies_of_hyps' $
  hs.foldl (λ ns h, ns.insert h.local_uniq_name) mk_name_set

/--
Given a set `ns` of unique names of hypotheses,
`reverse_dependencies_of_hyps_inclusive' hs` returns those hypotheses which
inclusively depend on any of the `hs`. See note [dependencies of hypotheses].

This is the 'revert closure' of `hs`: to revert the `hs`, we must also revert
their reverse dependencies.
-/
meta def reverse_dependencies_of_hyps_inclusive' (hs : name_set) :
  tactic (list expr) := do
  ctx ← local_context,
  ctx.mfilter $ λ h, hyp_depends_on_locals_inclusive h hs

/--
`reverse_dependencies_of_hyps_inclusive hs` returns those hypotheses which
inclusively depend on any of the hypotheses `hs`. See note
[dependencies of hypotheses].

This is the 'revert closure' of `hs`: to revert the `hs`, we must also revert
their reverse dependencies.
-/
meta def reverse_dependencies_of_hyps_inclusive (hs : list expr) :
  tactic (list expr) := do
reverse_dependencies_of_hyps_inclusive' $
  hs.foldl (λ ns h, ns.insert h.local_uniq_name) mk_name_set

/--
Revert the local constants whose unique names appear in `hs`, as well as any
hypotheses that depend on them. Returns the number of reverted hypotheses and a
list containing these hypotheses. The returned hypotheses are arbitrarily
ordered and are guaranteed to store the correct type (see `tactic.update_type`).
-/
meta def revert_set (hs : name_set) : tactic (ℕ × list expr) := do
  to_revert ← reverse_dependencies_of_hyps_inclusive' hs,
  to_revert_with_types ← to_revert.mmap update_type,
  num_reverted ← revert_lst to_revert,
  pure (num_reverted, to_revert_with_types)

/--
Revert the local constants in `hs`, as well as any hypotheses that depend on
them. Returns the number of reverted hypotheses and a list containing these
hypotheses. The returned hypotheses are arbitrarily ordered and are guaranteed
to store the correct type (see `tactic.update_type`).
-/
meta def revert_lst' (hs : list expr) : tactic (ℕ × list expr) :=
revert_set $ hs.foldl (λ ns h, ns.insert h.local_uniq_name) mk_name_set

/--
`revert_reverse_dependencies_of_hyp h` reverts all the hypotheses that depend on
the hypothesis `h`, including the local definitions that have `h` in their
value. This fixes a bug in `revert_kdeps` that does not revert local definitions
for which `h` only appears in the value. Returns the number of reverted
hypotheses.
-/
meta def revert_reverse_dependencies_of_hyp (h : expr) : tactic ℕ :=
reverse_dependencies_of_hyps [h] >>= revert_lst
/- We cannot implement it as `revert e >> intro1` because that would change the
local constant in the context. -/

/--
`revert_reverse_dependencies_of_hyp hs` reverts all the hypotheses that depend
on a hypothesis in `hs`. The `hs` themselves are not reverted, unless they
depend on each other. Returns the number of reverted hypotheses.
-/
meta def revert_reverse_dependencies_of_hyps (hs : list expr) : tactic ℕ :=
reverse_dependencies_of_hyps hs >>= revert_lst

end tactic

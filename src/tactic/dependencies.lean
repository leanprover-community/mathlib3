/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import tactic.core

/-!
# Tactics About Dependencies

This module provides tactics to compute dependencies and reverse dependencies of
hypotheses. An expression `e` depends on a hypothesis `h` if `e` would not be
valid if `h` were removed from the context. For example, the expression `e = x >
0` depends on `x`. We say that `x` is a dependency of `e` and that `e` is a
reverse dependency of `x`.

It is sometimes useful to consider *inclusive* dependency: `e` inclusively
depends on `h` iff `e` depends on `h` or `e = h` (so inclusive dependency is the
reflexive closure of regular dependency).

Note that the standard library does not use quite the same terminology:

* `kdependencies`/`kdeps` from the standard library compute reverse
  dependencies, not dependencies.
* `kdepends_on` and functions derived from it ignore local definitions and
  therefore compute a weaker dependency relation (see next section).

## Local Definitions

Determining dependencies of hypotheses is usually straightforward: a hypothesis
`r : R` depends on another hypothesis `d : D` if `d` occurs in `R`. The
implementation is more involved, however, in the presence of local definitions.
Consider this context:

```lean
n m : ℕ
k : ℕ := m
o : ℕ := k
h : o > 0
```

`h` depends on `o`, `k` and `m`, but only the dependency on `o` is syntactically
obvious. `kdepends_on` ignores this complication and claims that `h` does not
depend on `k` or `m`. We do not follow this example but process local
definitions properly. When determining whether `r : R` depends on `d : D`, we
first check whether the context up to `r` contains any local definitions. If
not, we can simply check whether `d` occurs in `R`. But if there are local
definitions, we must compute the transitive dependencies of all hypotheses up to
`r`.

If you want to ignore local definitions while computing dependencies, this
module also provides tactics to find the *direct* dependencies of a hypothesis.
These are the hypotheses that syntactically appear in the hypothesis's type (or
value, if the hypothesis is a local definition).
-/

open native
open expr_set (local_set_to_name_set)

namespace tactic

private meta def local_list_to_name_set (lcs : list expr) : name_set :=
lcs.foldl (λ ns h, ns.insert h.local_uniq_name) mk_name_set

/-! ### Direct Dependencies -/

/--
`type_has_local_in_name_set h ns` returns true iff the type of `h` contains a
local constant whose unique name appears in `ns`.
-/
meta def type_has_local_in_name_set (h : expr) (ns : name_set) : tactic bool := do
  h_type ← infer_type h,
  pure $ h_type.has_local_in ns

/--
`type_has_local_in_set h hs` returns true iff the type of `h` contains any of
the local constants `hs`.
-/
meta def type_has_local_in_set (h : expr) (hs : expr_set) : tactic bool :=
type_has_local_in_name_set h $ local_set_to_name_set hs

/--
`type_has_local_in h hs` returns true iff the type of `h` contains any of the
local constants `hs`.
-/
meta def type_has_local_in (h : expr) (hs : list expr) : tactic bool :=
type_has_local_in_name_set h $ local_list_to_name_set hs

/--
`local_def_value_has_local_in_name_set h ns` returns true iff `h` is a local
definition whose value contains a local constant whose unique name appears in
`ns`.
-/
meta def local_def_value_has_local_in_name_set (h : expr) (ns : name_set) :
  tactic bool := do
  (some h_val) ← try_core $ local_def_value h | pure ff,
  pure $ h_val.has_local_in ns

/--
`local_def_value_has_local_in_set h hs` returns true iff `h` is a local
definition whose value contains any of the local constants `hs`.
-/
meta def local_def_value_has_local_in_set (h : expr) (hs : expr_set) :
  tactic bool :=
local_def_value_has_local_in_name_set h $ local_set_to_name_set hs

/--
`local_def_value_has_local_in h hs` returns true iff `h` is a local definition
whose value contains any of the local constants `hs`.
-/
meta def local_def_value_has_local_in (h : expr) (hs : list expr) :
  tactic bool :=
local_def_value_has_local_in_name_set h $ local_list_to_name_set hs

/--
`direct_dependency_set_of_hyp h` is the set of hypotheses that the hypothesis
`h` directly depends on. These are the hypotheses that appear in `h`'s type or
value (if `h` is a local definition).
-/
meta def direct_dependency_set_of_hyp (h : expr) : tactic expr_set := do
  t ← infer_type h,
  let deps := t.list_local_consts',
  (some val) ← try_core $ local_def_value h | pure deps,
  let deps := deps.union val.list_local_consts',
  pure deps

/--
`direct_dependency_name_set_of_hyp h` is the set of unique names of hypotheses
that the hypothesis `h` directly depends on. These are the hypotheses that
appear in `h`'s type or value (if `h` is a local definition).
-/
meta def direct_dependency_name_set_of_hyp (h : expr) : tactic name_set :=
local_set_to_name_set <$> direct_dependency_set_of_hyp h

/--
`direct_dependencies_of_hyp h` is the list of hypotheses that the hypothesis `h`
directly depends on. These are the hypotheses that appear in `h`'s type or value
(if `h` is a local definition). The dependencies are returned in no particular
order.
-/
meta def direct_dependencies_of_hyp (h : expr) : tactic (list expr) :=
rb_set.to_list <$> direct_dependency_set_of_hyp h

/--
`direct_dependency_set_of_hyp_inclusive h` is the set of hypotheses that the
hypothesis `h` directly depends on, plus `h` itself.
-/
meta def direct_dependency_set_of_hyp_inclusive (h : expr) : tactic expr_set := do
  deps ← direct_dependency_set_of_hyp h,
  pure $ deps.insert h

/--
`direct_dependency_name_set_of_hyp_inclusive h` is the set of unique names of
hypotheses that the hypothesis `h` directly depends on, plus `h` itself.
-/
meta def direct_dependency_name_set_of_hyp_inclusive (h : expr) :
  tactic name_set :=
local_set_to_name_set <$> direct_dependency_set_of_hyp_inclusive h

/--
`direct_dependencies_of_hyp_inclusive h` is the list of hypotheses that the
hypothesis `h` directly depends on, plus `h` itself. The dependencies are
returned in no particular order.
-/
meta def direct_dependencies_of_hyp_inclusive (h : expr) : tactic (list expr) :=
rb_set.to_list <$> direct_dependency_set_of_hyp_inclusive h

/--
`hyp_directly_depends_on_local_name_set h ns` is true iff the hypothesis `h`
directly depends on a hypothesis whose unique name appears in `ns`.
-/
meta def hyp_directly_depends_on_local_name_set (h : expr) (ns : name_set) :
  tactic bool :=
list.mbor
  [ type_has_local_in_name_set h ns,
    local_def_value_has_local_in_name_set h ns ]

/--
`hyp_directly_depends_on_local_set h hs` is true iff the hypothesis `h` directly
depends on any of the hypotheses `hs`.
-/
meta def hyp_directly_depends_on_local_set (h : expr) (hs : expr_set) :
  tactic bool :=
hyp_directly_depends_on_local_name_set h $ local_set_to_name_set hs

/--
`hyp_directly_depends_on_locals h hs` is true iff the hypothesis `h` directly
depends on any of the hypotheses `hs`.
-/
meta def hyp_directly_depends_on_locals (h : expr) (hs : list expr) :
  tactic bool :=
hyp_directly_depends_on_local_name_set h $ local_list_to_name_set hs


/-! ### (Indirect) Dependencies -/

/--
`context_dependencies ctx` is a map associating each hypothesis `r ∈ ctx` with
those hypotheses `d ∈ ctx` which `r` depends on. `ctx` must be a sublist of the
local context. In particular, the hypotheses in `ctx` must be in context order,
so earlier hypotheses may not depend on later hypotheses.
-/
meta def context_dependencies (ctx : list expr) : tactic (expr_map expr_set) :=
ctx.mfoldl
  (λ deps h, do
    direct_deps ← direct_dependency_set_of_hyp h,
    let trans_deps := direct_deps.fold direct_deps $ λ dep trans_deps,
      trans_deps.union $ (deps.find dep).get_or_else mk_expr_set,
    pure $ deps.insert h trans_deps
    )
  mk_expr_map

/--
`hyp_depends_on_local_name_set h ns` is true iff the hypothesis `h` depends on
any of the hypotheses whose unique names appear in `ns`.

This tactic is moderately expensive if the context up to `h` contains local
definitions. If you need to check dependencies of multiple hypotheses, you may
want to use `tactic.context_dependencies`.
-/
meta def hyp_depends_on_local_name_set (h : expr) (ns : name_set) : tactic bool := do
  ctx ← local_context,
  let ctx := ctx.take_while (≠ h) ++ [h],
  ctx_has_local_def ← ctx.many (succeeds ∘ local_def_value),
  if ¬ ctx_has_local_def
    then hyp_directly_depends_on_local_name_set h ns
    else do
      deps ← context_dependencies ctx,
      let h_deps := local_set_to_name_set $ (deps.find h).get_or_else mk_expr_set,
      pure $ ns.fold ff (λ dep b, b || h_deps.contains dep)

/--
`hyp_depends_on_local_set h hs` is true iff the hypothesis `h` depends on
any of the hypotheses `hs`. See `tactic.hyp_depends_on_local_name_set`.
-/
meta def hyp_depends_on_local_set (h : expr) (hs : expr_set) : tactic bool :=
hyp_depends_on_local_name_set h $ local_set_to_name_set hs

/--
`hyp_depends_on_locals h hs` is true iff the hypothesis `h` depends on any of
the hypotheses `hs`. See `tactic.hyp_depends_on_local_name_set`.
-/
meta def hyp_depends_on_locals (h : expr) (hs : list expr) : tactic bool :=
hyp_depends_on_local_name_set h $ local_list_to_name_set hs

/--
`hyp_depends_on_local_name_set_inclusive h ns` is true iff the hypothesis `h`
inclusively depends on any of the hypotheses whose unique names appear in `ns`.
This is the case if either `h` depends on any of the `ns` or `h` itself appears
in `ns`.

This tactic is moderately expensive if the context up to `h` contains local
definitions. If you need to check dependencies of multiple hypotheses, you may
want to use `tactic.context_dependencies`.
-/
meta def hyp_depends_on_local_name_set_inclusive (h : expr) (ns : name_set) :
  tactic bool :=
list.mbor
  [ pure $ ns.contains h.local_uniq_name,
    hyp_depends_on_local_name_set h ns ]

/--
`hyp_depends_on_local_set_inclusive h hs` is true iff the hypothesis `h`
depends on any of the hypotheses `hs`. See
`tactic.hyp_depends_on_local_name_set_inclusive`.
-/
meta def hyp_depends_on_local_set_inclusive (h : expr) (hs : expr_set) :
  tactic bool :=
hyp_depends_on_local_name_set_inclusive h $ local_set_to_name_set hs

/--
`hyp_depends_on_locals_inclusive h hs` is true iff the hypothesis `h` depends on
any of the hypotheses `hs`. See
`tactic.hyp_depends_on_local_name_set_inclusive`.
-/
meta def hyp_depends_on_locals_inclusive (h : expr) (hs : list expr) :
  tactic bool :=
hyp_depends_on_local_name_set_inclusive h $ local_list_to_name_set hs

/--
`dependency_set_of_hyp h` is the set of dependencies of the hypothesis `h`.

This tactic is moderately expensive if the context up to `h` contains local
definitions. If you need the dependencies of multiple hypotheses, you may want
to use `tactic.context_dependencies`.
-/
meta def dependency_set_of_hyp (h : expr) : tactic expr_set := do
  ctx ← local_context,
  let ctx := ctx.take_while (≠ h) ++ [h],
  ctx_has_local_def ← ctx.many (succeeds ∘ local_def_value),
  if ¬ ctx_has_local_def
    then direct_dependency_set_of_hyp h
    else do
      deps ← context_dependencies ctx,
      pure $ (deps.find h).get_or_else mk_expr_set

/--
`dependency_name_set_of_hyp h` is the set of unique names of the dependencies of
the hypothesis `h`. See `tactic.dependency_set_of_hyp`.
-/
meta def dependency_name_set_of_hyp (h : expr) : tactic name_set :=
local_set_to_name_set <$> dependency_set_of_hyp h

/--
`dependencies_of_hyp h` is the list of dependencies of the hypothesis `h`. See
`tactic.dependency_set_of_hyp`. The dependencies are returned in no particular
order.
-/
meta def dependencies_of_hyp (h : expr) : tactic (list expr) :=
rb_set.to_list <$> dependency_set_of_hyp h

/--
`dependency_set_of_hyp_inclusive h` is the set of dependencies of the hypothesis
`h`, plus `h` itself.

This tactic is moderately expensive if the context up to `h` includes local
definitions. If you need the dependencies of multiple hypotheses, you may want
to use `tactic.context_dependencies`.
-/
meta def dependency_set_of_hyp_inclusive (h : expr) : tactic expr_set := do
  deps ← dependency_set_of_hyp h,
  pure $ deps.insert h

/--
`dependency_name_set_of_hyp_inclusive h` is the set of unique names of the
dependencies of the hypothesis `h`, plus `h` itself. See
`tactic.dependency_set_of_hyp_inclusive`.
-/
meta def dependency_name_set_of_hyp_inclusive (h : expr) : tactic name_set :=
local_set_to_name_set <$> dependency_set_of_hyp_inclusive h

/--
`dependencies_of_hyp_inclusive h` is the list of dependencies of the hypothesis
`h`, plus `h` itself. See `tactic.dependency_set_of_hyp_inclusive`. The
dependencies are returned in no particular order.
-/
meta def dependencies_of_hyp_inclusive (h : expr) : tactic (list expr) :=
rb_set.to_list <$> dependency_set_of_hyp_inclusive h


/-! ### Reverse Dependencies -/

private meta def reverse_dependencies_of_hyp_name_set_aux (hs : name_set) :
  list expr → list expr → name_set → tactic (list expr)
| [] revdeps _ := pure revdeps.reverse
| (H :: Hs) revdeps ns := do
  let H_uname := H.local_uniq_name,
  H_is_revdep ← list.mband
    [ pure $ ¬ hs.contains H_uname,
      hyp_directly_depends_on_local_name_set H ns ],
  if H_is_revdep
    then
      reverse_dependencies_of_hyp_name_set_aux Hs (H :: revdeps)
        (ns.insert H_uname)
    else
      reverse_dependencies_of_hyp_name_set_aux Hs revdeps ns

/--
`reverse_dependencies_of_hyp_name_set hs` is the list of reverse dependencies of
the hypotheses whose unique names appear in `hs`, excluding the `hs` themselves.
The reverse dependencies are returned in the order in which they appear in the
context.
-/
meta def reverse_dependencies_of_hyp_name_set (hs : name_set) :
  tactic (list expr) := do
  ctx ← local_context,
  let ctx := ctx.after (λ h, hs.contains h.local_uniq_name),
  reverse_dependencies_of_hyp_name_set_aux hs ctx [] hs

/--
`reverse_dependencies_of_hyp_set hs` is the list of reverse dependencies of the
hypotheses `hs`, excluding the `hs` themselves. The reverse dependencies are
returned in the order in which they appear in the context.
-/
meta def reverse_dependencies_of_hyp_set (hs : expr_set) : tactic (list expr) :=
reverse_dependencies_of_hyp_name_set $ local_set_to_name_set hs

/--
`reverse_dependencies_of_hyps hs` is the list of reverse dependencies of the
hypotheses `hs`, excluding the `hs` themselves. The reverse dependencies are
returned in the order in which they appear in the context.
-/
meta def reverse_dependencies_of_hyps (hs : list expr) : tactic (list expr) :=
reverse_dependencies_of_hyp_name_set $ local_list_to_name_set hs

private meta def reverse_dependencies_of_hyp_name_set_inclusive_aux :
  list expr → list expr → name_set → tactic (list expr)
| [] revdeps _ := pure revdeps.reverse
| (H :: Hs) revdeps ns := do
  let H_uname := H.local_uniq_name,
  H_is_revdep ← list.mbor
    [ pure $ ns.contains H.local_uniq_name,
      hyp_directly_depends_on_local_name_set H ns ],
  if H_is_revdep
    then
      reverse_dependencies_of_hyp_name_set_inclusive_aux Hs (H :: revdeps)
        (ns.insert H_uname)
    else
      reverse_dependencies_of_hyp_name_set_inclusive_aux Hs revdeps ns

/--
`reverse_dependencies_of_hyp_name_set_inclusive hs` is the list of reverse
dependencies of the hypotheses whose unique names appear in `hs`, including the
`hs` themselves. The reverse dependencies are returned in the order in which
they appear in the context.
-/
meta def reverse_dependencies_of_hyp_name_set_inclusive (hs : name_set) :
  tactic (list expr) := do
  ctx ← local_context,
  let ctx := ctx.drop_while (λ h, ¬ hs.contains h.local_uniq_name),
  reverse_dependencies_of_hyp_name_set_inclusive_aux ctx [] hs

/--
`reverse_dependencies_of_hyp_set_inclusive hs` is the list of reverse
dependencies of the hypotheses `hs`, including the `hs` themselves. The
inclusive reverse dependencies are returned in the order in which they appear in
the context.
-/
meta def reverse_dependencies_of_hyp_set_inclusive (hs : expr_set) :
  tactic (list expr) :=
reverse_dependencies_of_hyp_name_set_inclusive $ local_set_to_name_set hs

/--
`reverse_dependencies_of_hyps_inclusive hs` is the list of reverse dependencies
of the hypotheses `hs`, including the `hs` themselves. The reverse dependencies
are returned in the order in which they appear in the context.
-/
meta def reverse_dependencies_of_hyps_inclusive (hs : list expr) :
  tactic (list expr) :=
reverse_dependencies_of_hyp_name_set_inclusive $ local_list_to_name_set hs

/-! ### Reverting -/

/--
`revert_name_set hs` reverts the local constants whose unique names appear
in `hs` as well as any hypotheses that depend on them. Returns the number of
reverted hypotheses and a list containing these hypotheses. The returned
hypotheses are arbitrarily ordered and are guaranteed to store the correct type
(see `tactic.update_type`). -/
meta def revert_name_set (hs : name_set) : tactic (ℕ × list expr) := do
  to_revert ← reverse_dependencies_of_hyp_name_set_inclusive hs,
  to_revert_with_types ← to_revert.mmap update_type,
  num_reverted ← revert_lst to_revert,
  pure (num_reverted, to_revert_with_types)

/--
`revert_set hs` reverts the local constants in `hs`, as well as any
hypotheses that depend on them. Returns the number of reverted hypotheses and a
list containing these hypotheses. The returned hypotheses are arbitrarily
ordered and are guaranteed to store the correct type (see `tactic.update_type`).
-/
meta def revert_set (hs : expr_set) : tactic (ℕ × list expr) :=
revert_name_set $ local_set_to_name_set hs

/--
`revert_lst' hs` reverts the local constants in `hs`, as well as any
hypotheses that depend on them. Returns the number of reverted hypotheses and a
list containing these hypotheses. The returned hypotheses are arbitrarily
ordered and are guaranteed to store the correct type (see `tactic.update_type`).
-/
meta def revert_lst' (hs : list expr) : tactic (ℕ × list expr) :=
revert_name_set $ local_list_to_name_set hs

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
`revert_reverse_dependencies_of_hyp_name_set hs` reverts all the hypotheses that
depend on a hypothesis whose unique name appears in `hs`. The `hs` themselves
are not reverted, unless they depend on each other. Returns the number of
reverted hypotheses.
-/
meta def revert_reverse_dependencies_of_hyp_name_set (hs : name_set) : tactic ℕ :=
reverse_dependencies_of_hyp_name_set hs >>= revert_lst

/--
`revert_reverse_dependencies_of_hyp_set hs` reverts all the hypotheses that
depend on a hypothesis in `hs`. The `hs` themselves are not reverted, unless
they depend on each other. Returns the number of reverted hypotheses.
-/
meta def revert_reverse_dependencies_of_hyp_set (hs : expr_set) : tactic ℕ :=
reverse_dependencies_of_hyp_set hs >>= revert_lst

/--
`revert_reverse_dependencies_of_hyp hs` reverts all the hypotheses that depend
on a hypothesis in `hs`. The `hs` themselves are not reverted, unless they
depend on each other. Returns the number of reverted hypotheses.
-/
meta def revert_reverse_dependencies_of_hyps (hs : list expr) : tactic ℕ :=
reverse_dependencies_of_hyps hs >>= revert_lst

end tactic

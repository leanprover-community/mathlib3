/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import tactic.core

/-!
# simp_result

`dsimp_result` and `simp_result` are a pair of tactics for
cleaning up the results produced by other tactics.

They should be used with some caution.
You should consider whether there is any real need for this clean-up,
and whether there is a more direct way of producing the result you wanted,
before relying on these tactics.

Both are implemented in terms of a generic `intercept_result` tactic,
which allows you to run an arbitrary tactic and modify the returned results.
-/

namespace tactic

/--
`intercept_result m t`
attempts to run a tactic `t`,
intercepts any results `t` assigns to the goals,
and runs `m : expr → tactic expr` on each of the expressions
before assigning the returned values to the original goals.
-/
meta def intercept_result {α} (m : expr → tactic expr) (t : tactic α) : tactic α := do
-- Replace the goals with copies.
gs ← get_goals,
gs' ← gs.mmap (λ g, infer_type g >>= mk_meta_var),
set_goals gs',
-- Run the tactic on the copied goals.
a ← t,
-- Run `m` on the produced terms,
(gs.zip gs').mmap (λ ⟨g, g'⟩, do
  g' ← instantiate_mvars g',
  g'' ← with_local_goals' gs $ m g',
  -- and assign to the original goals.
  -- (We have to use `assign` here, as `unify` and `exact` are apparently
  -- a bit unreliable about which way they do the assignment!)
  unsafe.type_context.run $ unsafe.type_context.assign g g''),
pure a

/--
`dsimp_result t`
attempts to run a tactic `t`,
intercepts any results it assigns to the goals,
and runs `dsimp` on those results
before assigning the simplified values to the original goals.
-/
meta def dsimp_result {α}
  (cfg : dsimp_config := { fail_if_unchanged := ff }) (no_defaults := ff)
  (attr_names : list name := []) (hs : list simp_arg_type := [])
  (t : tactic α) : tactic α :=
intercept_result (λ g,
  g.dsimp cfg no_defaults attr_names hs) t

/--
`simp_result t`
attempts to run a tactic `t`,
intercepts any results `t` assigns to the goals,
and runs `simp` on those results
before assigning the simplified values to the original goals.
-/
meta def simp_result {α}
  (cfg : simp_config := { fail_if_unchanged := ff }) (discharger : tactic unit := failed) (no_defaults := ff)
  (attr_names : list name := []) (hs : list simp_arg_type := [])
  (t : tactic α) : tactic α :=
intercept_result (λ g, prod.fst <$>
  g.simp cfg discharger no_defaults attr_names hs) t

namespace interactive
open interactive interactive.types

/--
`dsimp_result { tac }`
attempts to run a tactic block `tac`,
intercepts any results the tactic block would have assigned to the goals,
and runs `dsimp` on those results
before assigning the simplified values to the original goals.

You can use the usual interactive syntax for `dsimp`, e.g.
`dsimp_result only [a, b, c] with attr { tac }`.
-/
meta def dsimp_result
  (no_defaults : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list)
  (t : itactic) : itactic :=
tactic.dsimp_result { fail_if_unchanged := ff } no_defaults attr_names hs t

/--
`simp_result { tac }`
attempts to run a tactic block `tac`,
intercepts any results the tactic block would have assigned to the goals,
and runs `simp` on those results
before assigning the simplified values to the original goals.

You can use the usual interactive syntax for `simp`, e.g.
`simp_result only [a, b, c] with attr { tac }`.
-/
meta def simp_result
  (no_defaults : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list)
  (t : itactic) : itactic :=
tactic.simp_result { fail_if_unchanged := ff } failed no_defaults attr_names hs t

add_tactic_doc
{ name       := "simp_result",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.simp_result],
  tags       := ["simplification"] }

add_tactic_doc
{ name       := "dsimp_result",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.dsimp_result],
  tags       := ["simplification"] }

end interactive
end tactic

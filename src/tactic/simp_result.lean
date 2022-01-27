/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Scott Morrison
-/
import tactic.core

/-!
# simp_result

`dsimp_result` and `simp_result` are a pair of tactics for
applying `dsimp` or `simp` to the result produced by other tactics.

As examples, tactics which use `revert` and `intro`
may insert additional `id` terms in the result they produce.
If there is some reason these are undesirable
(e.g. the result term needs to be human-readable, or
satisfying syntactic rather than just definitional properties),
wrapping those tactics in `dsimp_result`
can remove the `id` terms "after the fact".

Similarly, tactics using `subst` and `rw` will nearly always introduce `eq.rec` terms,
but sometimes these will be easy to remove,
for example by simplifying using `eq_rec_constant`.
This is a non-definitional simplification lemma,
and so wrapping these tactics in `simp_result` will result
in a definitionally different result.

There are several examples in the associated test file,
demonstrating these interactions with `revert` and `subst`.

These tactics should be used with some caution.
You should consider whether there is any real need for the simplification of the result,
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

Because `intercept_result` uses `unsafe.type_context.assign` rather than `unify`,
if the tactic `m` does something unreasonable
you may produce terms that don't typecheck,
possibly with mysterious error messages.
Be careful!
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
  -- unreliable about which way they do the assignment!)
  unsafe.type_context.run $ unsafe.type_context.assign g g''),
pure a

/--
`dsimp_result t`
attempts to run a tactic `t`,
intercepts any results it assigns to the goals,
and runs `dsimp` on those results
before assigning the simplified values to the original goals.
-/
meta def dsimp_result {α} (t : tactic α)
  (cfg : dsimp_config := { fail_if_unchanged := ff }) (no_defaults := ff)
  (attr_names : list name := []) (hs : list simp_arg_type := []) : tactic α :=
intercept_result (λ g,
  g.dsimp cfg no_defaults attr_names hs) t

/--
`simp_result t`
attempts to run a tactic `t`,
intercepts any results `t` assigns to the goals,
and runs `simp` on those results
before assigning the simplified values to the original goals.
-/
meta def simp_result {α} (t : tactic α)
  (cfg : simp_config := { fail_if_unchanged := ff }) (discharger : tactic unit := failed)
  (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) : tactic α :=
intercept_result (λ g, prod.fst <$>
  g.simp cfg discharger no_defaults attr_names hs) t

namespace interactive
setup_tactic_parser

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
tactic.dsimp_result t { fail_if_unchanged := ff } no_defaults attr_names hs

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
tactic.simp_result t { fail_if_unchanged := ff } failed no_defaults attr_names hs

/--
`simp_result { tac }`
attempts to run a tactic block `tac`,
intercepts any results the tactic block would have assigned to the goals,
and runs `simp` on those results
before assigning the simplified values to the original goals.

You can use the usual interactive syntax for `simp`, e.g.
`simp_result only [a, b, c] with attr { tac }`.

`dsimp_result { tac }` works similarly, internally using `dsimp`
(and so only simplifiying along definitional lemmas).
-/
add_tactic_doc
{ name       := "simp_result",
  category   := doc_category.tactic,
  decl_names := [``simp_result, ``dsimp_result],
  tags       := ["simplification"] }

end interactive
end tactic

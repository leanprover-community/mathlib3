/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Simon Hudon, Scott Morrison
-/
import tactic.equiv_rw

/-!
## The `transport` tactic

`transport` attempts to move an `s : S α` expression across an equivalence `e : α ≃ β` to solve
a goal of the form `S β`, by building the new object field by field, taking each field of `s`
and rewriting it along `e` using the `equiv_rw` tactic.

We try to ensure good definitional properties, so that, for example, when we transport a `monoid α`
to a `monoid β`, the new multiplication is definitionally `λ x y, e (e.symm a * e.symm b)`.
-/

namespace tactic
open tactic.interactive

mk_simp_attribute transport_simps
"The simpset `transport_simps` is used by the tactic `transport`
to simplify certain expressions involving application of equivalences,
and trivial `eq.rec` or `ep.mpr` conversions.
It's probably best not to adjust it without understanding the algorithm used by `transport`."

attribute [transport_simps] eq_rec_constant eq_mpr_rfl
attribute [transport_simps] equiv.symm_apply_apply equiv.arrow_congr'_apply equiv.to_fun_as_coe

/--
Given `s : S α` for some structure `S` depending on a type `α`,
and an equivalence `e : α ≃ β`,
try to produce an `S β`,
by transporting data and axioms across `e` using `equiv_rw`.
-/
@[nolint unused_arguments] -- At present we don't actually use `s`; it's inferred in the `mk_app` call.
meta def transport (s e : expr) : tactic unit :=
do
  -- FIXME document this algorithm line by line!
  (_, α, β) ← infer_type e >>= relation_lhs_rhs <|>
    fail format!"second argument to `transport` was not an equivalence",
  seq `[refine_struct { .. }]
  (simp_result (do
    propagate_tags $ (do
    f ← get_current_field,
    mk_mapp f [α, none] >>= note f none,
    b ← target >>= is_prop,
    if b then (do
      unfold_projs_target,
      `[simp only [] with transport_simps],
      -- Explain/understand when this is/isn't appropriate, and don't just `try` it blindly.
      try $ under_binders $ to_expr ``((%%e).symm.injective) >>= apply,
      equiv_rw_hyp f e,
      get_local f >>= exact) <|>
      skip
    else try (do
      equiv_rw_hyp f e,
      get_local f >>= exact))))

namespace interactive
open lean.parser
open interactive interactive.types
open tactic

local postfix `?`:9001 := optional

/--
Given a goal `⊢ S β` for some parametrized structure type `S`, and an equivalence `e : α ≃ β`.
`transport along e` will look for a hypothesis `s : S α`,
and attempt to close the goal by transporting `s` across the equivalence `e`.

```lean
example {α : Type} [ring α] {β : Type} (e : α ≃ β) : ring β :=
by transport along e.
```

You can specify the object to transport using `transport s along e`.

`transport` works by attempting to copy each of the operations and axiom fields of `s`,
rewriting them using `equiv_rw e` and defining a new structure using these rewritten fields.

If it fails to fill in all the new fields, `transport` will produce new subgoals.
It's probably best to think about which missing `simp` lemmas would have allowed `transport`
to finish, rather than solving these goals by hand.
(This may require looking at the implementation of `tranport` to understand its algorithm;
there are several examples of "transport-by-hand" at the end of `test/equiv_rw.lean`,
which `transport` is an abstraction of.)
-/
meta def transport (s : parse texpr?) (e : parse $ (tk "along" *> ident)) : itactic :=
do
  s ← match s with
  | some s := to_expr s
  | none := (do
      t ← target,
      let n := t.get_app_fn.const_name,
      ctx ← local_context,
      ctx.any_of (λ e, guard (e.get_app_fn.const_name = n) >> return e))
  end,
  e ← get_local e,
  tactic.transport s e

end interactive

end tactic

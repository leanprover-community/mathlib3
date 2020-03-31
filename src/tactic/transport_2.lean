/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw

namespace tactic
open tactic.interactive

/--
Attempts to run a tactic (which should only operate on the main goal),
intercepts any result it assigns to the goal,
and runs `simp` on that
before assigning the simplified value to the original goal.
-/
meta def simp_result {α : Type} (t : tactic α) : tactic α :=
do
  (r, a) ← retrieve (do
    v :: _ ← get_goals,
    a ← t,
    v ← instantiate_mvars v,
    return (v, a)),
  prod.fst <$> r.simp {fail_if_unchanged := ff} >>= exact,
  return a

/--
Given `s : S α` for some structure `S` depending on a type `α`,
and an equivalence `e : α ≃ β`,
try to produce an `S β`,
by transporting data and axioms across `e` using `equiv_rw`.
-/
meta def transport (s e : expr) : tactic unit :=
simp_result $
do
  v :: _ ← get_goals,
  (_, α, β) ← infer_type e >>= relation_lhs_rhs <|>
    fail format!"second argument to `transport` was not an equivalence",
  seq `[refine_struct { .. }]
  (do
    propagate_tags $ (do
    f ← get_current_field,
    mk_mapp f [α, none] >>= note f none,
    b ← target >>= is_prop,
    if b then (do
      unfold_projs_target,
      `[simp only [eq_rec_constant, eq_mpr_rfl, equiv.symm_apply_apply, equiv.arrow_congr'_apply, equiv.to_fun_as_coe]],
      -- Explain/understand when this is/isn't appropriate, and don't just `try` it blindly.
      try $ under_binders $ to_expr ``((%%e).symm.injective) >>= apply,
      equiv_rw_hyp f e,
      get_local f >>= exact) <|>
      skip
    else try (do
      equiv_rw_hyp f e,
      get_local f >>= exact)))

namespace interactive
open lean.parser
open interactive interactive.types
open tactic

local postfix `?`:9001 := optional

/--
Given a goal `⊢ S β` for some parametrized structure type `S`,
`transport` will look for a hypothesis `s : S α` and an equivalence `e : α ≃ β`,
and attempt to close the goal by transporting `s` across the equivalence `e`.

```lean
example {α : Type} [ring α] {β : Type} (e : α ≃ β) : ring β :=
by transport.
```

You can specify the object to transport using `transport s`,
and the equivalence to transport across using `transport s with e`.
-/
meta def transport (s : parse texpr?) (e : parse $ (tk "with" *> ident)?) : itactic :=
do
  s ← match s with
  | some s := to_expr s
  | none := (do -- no object specified, try to find a hypothesis that looks like the target:
    S ← target >>= (λ t, match t with
    | expr.app S α := pure S
    | _ := fail "No object to transport specified, and target doesn't look like a parametrized type."
    end),
    find_local ``(%%S _))
  end,
  e ← match e with
  | some e := get_local e
  | none := do -- no equivalence specified, try to find a hypothesis of the right shape:
    (S, α) ← infer_type s >>= (λ t, match t with
    | expr.app S α := pure (S, α)
    | _ := fail format!"Object to transport doesn't look like a parametrized type: {s}"
    end),
    S ← whnf S,
    β ← target >>= (λ t, match t with
    | expr.app S' β := (do
      S' ← whnf S',
      (is_def_eq S' S >> pure β)
        <|> (do S ← pp S, S' ← pp S', fail format!"Target doesn't match expected type: {S'} ≠ {S}"))
    | _ := fail format!"Target doesn't match expected type: {S} _"
    end),
    find_local ``(%%α ≃ %%β)
  end,
  tactic.transport s e

end interactive

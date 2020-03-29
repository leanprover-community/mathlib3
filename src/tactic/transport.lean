/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw

namespace tactic
open tactic.interactive

/--
Given `s : S α` for some structure `S` depending on a type `α`,
and an equivalence `e : α ≃ β`,
try to produce an `S β`,
by transporting data and axioms across `e` using `equiv_rw`.
-/
meta def transport (s e : expr) : tactic unit :=
do
  (_, α, β) ← infer_type e >>= relation_lhs_rhs <|>
    fail format!"second argument to `transport` was not an equivalence",
  seq `[refine_struct { .. }]
  (do
    propagate_tags $ (do
    f ← get_current_field,
    mk_mapp f [none, s] >>= note f none,
    b ← target >>= is_prop,
    if b then try (do
      intros,
      to_expr ``((%%e).symm.injective) >>= apply,
      unfold_projs_target,
      `[simp], -- TODO squeeze_simp here?
      equiv_rw_hyp f e,
      get_local f >>= apply)
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
  | none := (do
    S ← target >>= (λ t, match t with
    | expr.app S α := pure S
    | _ := fail "No object to transport specified, and target doesn't look like a parametrized type."
    end),
    find_local ``(%%S _))
  end,
  e ← match e with
  | some e := get_local e
  | none := do
    -- FIXME this is a hack, that works fine for structures like `ring α`, but ...
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

end tactic

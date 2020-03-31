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

-- This part is a hack, and hopefully won't last once I understand how to
-- simplify the output from a tactic...

/-- Copy a declaration to a new name, first running `simp` on the body. -/
meta def simp_defn (d : declaration) (new_name : name) : tactic unit :=
do (levels, type, value, reducibility, trusted) ← pure (match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    (levels, type, value, reducibility, trusted)
  | _ := undefined
  end),
  prop ← is_prop type,
  value ← prod.fst <$> value.simp {fail_if_unchanged := ff},
  let new_decl := if prop then
      declaration.thm new_name levels type (task.pure value)
    else
      declaration.defn new_name levels type value reducibility trusted,
  updateex_env $ λ env, env.add new_decl

open lean.parser tactic interactive parser

/-- Copy a declaration to a new name, first running `simp` on the body. -/
@[user_command] meta def simp_defn_cmd (_ : parse $ tk "simp_defn") : lean.parser unit :=
do from_lemma ← ident,
   new_name ← ident,
   from_lemma_fully_qualified ← resolve_constant from_lemma,
  d ← get_decl from_lemma_fully_qualified <|>
    fail ("declaration " ++ to_string from_lemma ++ " not found"),
  tactic.simp_defn d new_name.

end tactic

-- This is an attempt at an alternative to `simp_defn` to copy a declaration.
-- It works on easy examples, e.g. `def f : ℕ := by simp_result { exact (id 0) }`
-- but `transport` breaks when wrapped in it.

-- namespace tactic
-- meta def simp_result (i : tactic unit) : tactic unit :=
-- do
--   gs ← get_goals,
--   gs' ← gs.mmap (λ g, infer_type g >>= mk_meta_var),
--   set_goals gs',
--   r ← i,
--   (gs.zip gs').mmap (λ p, instantiate_mvars p.2 >>= (λ e, prod.fst <$> expr.simp e) >>= unify p.1),
--   set_goals gs,
--   return r

-- namespace interactive
-- meta def simp_result (i : itactic) : itactic := tactic.simp_result i
-- end interactive

-- end tactic

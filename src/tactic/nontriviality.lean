/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import logic.nontrivial


/-!
# The `nontriviality` tactic.

-/

namespace tactic

/--
Tries to generate a `nontrivial α` instance by performing case analysis on
`subsingleton_or_nontrivial α`,
attempting to discharge the subsingleton branch using lemmas with `@[nontriviality]` attribute,
including `subsingleton.le` and `eq_iff_true_of_subsingleton`.
-/
meta def nontriviality_by_elim (α : expr) (lems : interactive.parse simp_arg_list) : tactic unit :=
do
  alternative ← to_expr ``(subsingleton_or_nontrivial %%α),
  n ← get_unused_name "_inst",
  tactic.cases alternative [n, n],
  (solve1 $ do
    reset_instance_cache,
    apply_instance <|>
      interactive.simp none none ff lems [`nontriviality] (interactive.loc.ns [none])) <|>
      fail format!"Could not prove goal assuming `subsingleton {α}`",
  reset_instance_cache

/--
Tries to generate a `nontrivial α` instance using `nontrivial_of_ne` or `nontrivial_of_lt`
and local hypotheses.
-/
meta def nontriviality_by_assumption (α : expr) : tactic unit :=
do
  n ← get_unused_name "_inst",
  to_expr ``(nontrivial %%α) >>= assert n,
  apply_instance <|> `[solve_by_elim [nontrivial_of_ne, nontrivial_of_lt]],
  reset_instance_cache

end tactic

namespace tactic.interactive

open tactic

setup_tactic_parser

/--
Attempts to generate a `nontrivial α` hypothesis.

The tactic first looks for an instance using `apply_instance`.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `nontrivial` instance directly.

Otherwise, it will perform a case split on `subsingleton α ∨ nontrivial α`, and attempt to discharge
the `subsingleton` goal using `simp [lemmas] with nontriviality`, where `[lemmas]` is a list of
additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using [lemmas]`.

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  assumption,
end
```

```
example {R : Type} [comm_ring R] {r s : R} : r * s = s * r :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  apply mul_comm,
end
```

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 :=
begin
  nontriviality R, -- there is now a `nontrivial R` hypothesis available.
  dec_trivial
end
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b :=
begin
  success_if_fail { nontriviality α }, -- Fails
  nontriviality α using [myeq], -- There is now a `nontrivial α` hypothesis available
  assumption
end
```
-/
meta def nontriviality (t : parse texpr?)
  (lems : parse (tk "using" *> simp_arg_list <|> pure [])) :
  tactic unit :=
do
  α ← match t with
  | some α := to_expr α
  | none :=
    (do t ← mk_mvar, e ← to_expr ``(@eq %%t _ _), target >>= unify e, return t) <|>
    (do t ← mk_mvar, e ← to_expr ``(@has_le.le %%t _ _ _), target >>= unify e, return t) <|>
    (do t ← mk_mvar, e ← to_expr ``(@ne %%t _ _), target >>= unify e, return t) <|>
    (do t ← mk_mvar, e ← to_expr ``(@has_lt.lt %%t _ _ _), target >>= unify e, return t) <|>
    fail "The goal is not an (in)equality, so you'll need to specify the desired `nontrivial α`
      instance by invoking `nontriviality α`."
  end,
  nontriviality_by_assumption α <|> nontriviality_by_elim α lems

add_tactic_doc
{ name                     := "nontriviality",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.nontriviality],
  tags                     := ["logic", "type class"] }

end tactic.interactive

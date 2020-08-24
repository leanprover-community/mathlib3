/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.lint

/-!
# Congruence and related tactics

This file contains the tactic `congr'`, which is an extension of `congr`, and various tactics
using `congr'` internally.

-/

open tactic
setup_tactic_parser

namespace tactic

/-- Apply the constant `iff_of_eq` to the goal. -/
meta def apply_iff_congr_core : tactic unit :=
applyc ``iff_of_eq

/-- The main part of the body for the loop in `congr'`. This will try to replace a goal `f x = f y`
 with `x = y`. Also has support for `==` and `↔`. -/
meta def congr_core' : tactic unit :=
do tgt ← target,
   apply_eq_congr_core tgt
   <|> apply_heq_congr_core
   <|> apply_iff_congr_core
   <|> fail "congr tactic failed"

/-- The main function in `convert_to`. Changes the goal to `r` and a proof obligation that the goal
  is equal to `r`. -/
meta def convert_to_core (r : pexpr) : tactic unit :=
do tgt ← target,
   h   ← to_expr ``(_ : %%tgt = %%r),
   rewrite_target h,
   swap

namespace interactive

/--
Same as the `congr` tactic, but takes an optional argument which gives
the depth of recursive applications. This is useful when `congr`
is too aggressive in breaking down the goal. For example, given
`⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`.
If, at any point, a subgoal matches a hypothesis then the subgoal will be closed. -/
meta def congr' : parse (with_desc "n" small_nat)? → tactic unit
| (some 0) := failed
| o        := focus1 (assumption <|> (congr_core' >>
  all_goals (reflexivity <|> `[apply proof_irrel_heq] <|>
             `[apply proof_irrel] <|> try (congr' (nat.pred <$> o)))))

add_tactic_doc
{ name       := "congr'",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.congr', `tactic.interactive.congr],
  tags       := ["congruence"],
  inherit_description_from := `tactic.interactive.congr' }

/--
The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine
e`, but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal. For example, in the proof state

```lean
n : ℕ,
e : prime (2 * n + 1)
⊢ prime (n + n + 1)
```

the tactic `convert e` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr'`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr' n`). In the example, `convert e using
1` would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.
-/
meta def convert (sym : parse (with_desc "←" (tk "<-")?)) (r : parse texpr)
  (n : parse (tk "using" *> small_nat)?) : tactic unit :=
do v ← mk_mvar,
   if sym.is_some
     then refine ``(eq.mp %%v %%r)
     else refine ``(eq.mpr %%v %%r),
   gs ← get_goals,
   set_goals [v],
   try (congr' n),
   gs' ← get_goals,
   set_goals $ gs' ++ gs

add_tactic_doc
{ name       := "convert",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.convert],
  tags       := ["congruence"] }

/--
`convert_to g using n` attempts to change the current goal to `g`, but unlike `change`,
it will generate equality proof obligations using `congr' n` to resolve discrepancies.
`convert_to g` defaults to using `congr' 1`.

`ac_change` is `convert_to` followed by `ac_refl`. It is useful for rearranging/reassociating
e.g. sums:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N :=
begin
  ac_change a + d + e + f + c + g + b ≤ _,
-- ⊢ a + d + e + f + c + g + b ≤ N
end
```
-/
meta def convert_to (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
match n with
  | none     := convert_to_core r >> `[congr' 1]
  | (some 0) := convert_to_core r
  | (some o) := convert_to_core r >> congr' o
end

/-- `ac_change g using n` is `convert_to g using n; try {ac_refl}`. -/
meta def ac_change (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
convert_to r n; try ac_refl

add_tactic_doc
{ name       := "convert_to",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.convert_to, `tactic.interactive.ac_change],
  tags       := ["congruence"],
  inherit_description_from := `tactic.interactive.convert_to }

end interactive

end tactic

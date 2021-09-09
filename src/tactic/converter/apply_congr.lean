/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Scott Morrison
-/
import tactic.interactive
import tactic.converter.interactive

/-!
## Introduce the `apply_congr` conv mode tactic.

`apply_congr` will apply congruence lemmas inside `conv` mode.
It is particularly useful when the automatically generated congruence lemmas
are not of the optimal shape. An example, described in the doc-string is
rewriting inside the operand of a `finset.sum`.
-/

open tactic

namespace conv.interactive
open interactive interactive.types lean.parser

local postfix `?`:9001 := optional


/--
Apply a congruence lemma inside `conv` mode.

When called without an argument `apply_congr` will try applying all lemmas marked with `@[congr]`.
Otherwise `apply_congr e` will apply the lemma `e`.

Recall that a goal that appears as `∣ X` in `conv` mode
represents a goal of `⊢ X = ?m`,
i.e. an equation with a metavariable for the right hand side.

To successfully use `apply_congr e`, `e` will need to be an equation
(possibly after function arguments),
which can be unified with a goal of the form `X = ?m`.
The right hand side of `e` will then determine the metavariable,
and `conv` will subsequently replace `X` with that right hand side.

As usual, `apply_congr` can create new goals;
any of these which are _not_ equations with a metavariable on the right hand side
will be hard to deal with in `conv` mode.
Thus `apply_congr` automatically calls `intros` on any new goals,
and fails if they are not then equations.

In particular it is useful for rewriting inside the operand of a `finset.sum`,
as it provides an extra hypothesis asserting we are inside the domain.

For example:

```lean
example (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m) :
  finset.sum S f = finset.sum S g :=
begin
  conv_lhs {
    -- If we just call `congr` here, in the second goal we're helpless,
    -- because we are only given the opportunity to rewrite `f`.
    -- However `apply_congr` uses the appropriate `@[congr]` lemma,
    -- so we get to rewrite `f x`, in the presence of the crucial `H : x ∈ S` hypothesis.
    apply_congr,
    skip,
    simp [h, H], }
end
```

In the above example, when the `apply_congr` tactic is called it gives the hypothesis `H : x ∈ S`
which is then used to rewrite the `f x` to `g x`.
-/
meta def apply_congr (q : parse texpr?) : conv unit :=
do
  congr_lemmas ← match q with
  -- If the user specified a lemma, use that one,
  | some e := do
    gs ← get_goals,
    e ← to_expr e, -- to_expr messes with the goals? (see tests)
    set_goals gs,
    return [e]
  -- otherwise, look up everything tagged `@[congr]`
  | none := do
    congr_lemma_names ← attribute.get_instances `congr,
    congr_lemma_names.mmap mk_const
  end,
  -- For every lemma:
  congr_lemmas.any_of (λ n,
    -- Call tactic.eapply
    seq' (tactic.eapply n >> tactic.skip)
    -- and then call `intros` on each resulting goal, and require that afterwards it's an equation.
        (tactic.intros >> (do `(_ = _) ← target, tactic.skip)))

add_tactic_doc {
  name := "apply_congr",
  category := doc_category.tactic,
  decl_names := [`conv.interactive.apply_congr],
  tags := ["conv", "congruence", "rewriting"]
}

end conv.interactive

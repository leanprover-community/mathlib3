/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import order.filter.prod

/-!
# Curried Filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides an operation (`filter.curry`) on filters which provides the equivalence
`∀ᶠ a in l, ∀ᶠ b in l', p (a, b) ↔ ∀ᶠ c in (l.curry l'), p c` (see `filter.eventually_curry_iff`).

To understand when this operation might arise, it is helpful to think of `∀ᶠ` as a combination of
the quantifiers `∃ ∀`. For instance, `∀ᶠ n in at_top, p n ↔ ∃ N, ∀ n ≥ N, p n`. A curried filter
yields the quantifier order `∃ ∀ ∃ ∀`. For instance,
`∀ᶠ n in at_top.curry at_top, p n ↔ ∃ M, ∀ m ≥ M, ∃ N, ∀ n ≥ N, p (m, n)`.

This is different from a product filter, which instead yields a quantifier order `∃ ∃ ∀ ∀`. For
instance, `∀ᶠ n in at_top ×ᶠ at_top, p n ↔ ∃ M, ∃ N, ∀ m ≥ M, ∀ n ≥ N, p (m, n)`. This makes it
clear that if something eventually occurs on the product filter, it eventually occurs on the curried
filter (see `filter.curry_le_prod` and `filter.eventually.curry`), but the converse is not true.

Another way to think about the curried versus the product filter is that tending to some limit on
the product filter is a version of uniform convergence (see `tendsto_prod_filter_iff`) whereas
tending to some limit on a curried filter is just iterated limits (see `tendsto.curry`).

## Main definitions

* `filter.curry`: A binary operation on filters which represents iterated limits

## Main statements

* `filter.eventually_curry_iff`: An alternative definition of a curried filter
* `filter.curry_le_prod`: Something that is eventually true on the a product filter is eventually
   true on the curried filter

## Tags

uniform convergence, curried filters, product filters
-/

namespace filter

variables {α β γ : Type*}

/-- This filter is characterized by `filter.eventually_curry_iff`:
`(∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y)`. Useful
in adding quantifiers to the middle of `tendsto`s. See
`has_fderiv_at_of_tendsto_uniformly_on_filter`. -/
def curry (f : filter α) (g : filter β) : filter (α × β) :=
{ sets := { s | ∀ᶠ (a : α) in f, ∀ᶠ (b : β) in g, (a, b) ∈ s },
  univ_sets := (by simp only [set.mem_set_of_eq, set.mem_univ, eventually_true]),
  sets_of_superset := begin
    intros x y hx hxy,
    simp only [set.mem_set_of_eq] at hx ⊢,
    exact hx.mono (λ a ha, ha.mono(λ b hb, set.mem_of_subset_of_mem hxy hb)),
  end,
  inter_sets := begin
    intros x y hx hy,
    simp only [set.mem_set_of_eq, set.mem_inter_iff] at hx hy ⊢,
    exact (hx.and hy).mono (λ a ha, (ha.1.and ha.2).mono (λ b hb, hb)),
  end, }

lemma eventually_curry_iff {f : filter α} {g : filter β} {p : α × β → Prop} :
  (∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y) :=
iff.rfl

lemma curry_le_prod {f : filter α} {g : filter β} :
  f.curry g ≤ f.prod g :=
begin
  intros u hu,
  rw ←eventually_mem_set at hu ⊢,
  rw eventually_curry_iff,
  exact hu.curry,
end

lemma tendsto.curry {f : α → β → γ} {la : filter α} {lb : filter β} {lc : filter γ} :
  (∀ᶠ a in la, tendsto (λ b : β, f a b) lb lc) → tendsto ↿f (la.curry lb) lc :=
begin
  intros h,
  rw tendsto_def,
  simp only [curry, filter.mem_mk, set.mem_set_of_eq, set.mem_preimage],
  simp_rw tendsto_def at h,
  refine (λ s hs, h.mono (λ a ha, eventually_iff.mpr _)),
  simpa [function.has_uncurry.uncurry, set.preimage] using ha s hs,
end

end filter

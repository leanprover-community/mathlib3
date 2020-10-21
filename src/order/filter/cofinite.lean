/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import order.filter.at_top_bot

/-!
# The cofinite filter

In this file we define

`cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `at_top`.

## TODO

Define filters for other cardinalities of the complement.
-/

open set
open_locale classical

variables {α : Type*}

namespace filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : filter α :=
{ sets             := {s | finite sᶜ},
  univ_sets        := by simp only [compl_univ, finite_empty, mem_set_of_eq],
  sets_of_superset := assume s t (hs : finite sᶜ) (st: s ⊆ t),
    hs.subset $ compl_subset_compl.2 st,
  inter_sets       := assume s t (hs : finite sᶜ) (ht : finite (tᶜ)),
    by simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq] }

@[simp] lemma mem_cofinite {s : set α} : s ∈ (@cofinite α) ↔ finite sᶜ := iff.rfl

instance cofinite_ne_bot [infinite α] : ne_bot (@cofinite α) :=
mt empty_in_sets_eq_bot.mpr $ by { simp only [mem_cofinite, compl_empty], exact infinite_univ }

lemma frequently_cofinite_iff_infinite {p : α → Prop} :
  (∃ᶠ x in cofinite, p x) ↔ set.infinite {x | p x} :=
by simp only [filter.frequently, filter.eventually, mem_cofinite, compl_set_of, not_not,
  set.infinite]

end filter

open filter

lemma set.finite.compl_mem_cofinite {s : set α} (hs : s.finite) : sᶜ ∈ (@cofinite α) :=
mem_cofinite.2 $ (compl_compl s).symm ▸ hs

lemma set.finite.eventually_cofinite_nmem {s : set α} (hs : s.finite) : ∀ᶠ x in cofinite, x ∉ s :=
hs.compl_mem_cofinite

lemma finset.eventually_cofinite_nmem (s : finset α) : ∀ᶠ x in cofinite, x ∉ s :=
s.finite_to_set.eventually_cofinite_nmem

lemma set.infinite_iff_frequently_cofinite {s : set α} :
  set.infinite s ↔ (∃ᶠ x in cofinite, x ∈ s) :=
frequently_cofinite_iff_infinite.symm

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
lemma nat.cofinite_eq_at_top : @cofinite ℕ = at_top :=
begin
  ext s,
  simp only [mem_cofinite, mem_at_top_sets],
  split,
  { assume hs,
    use (hs.to_finset.sup id) + 1,
    assume b hb,
    by_contradiction hbs,
    have := hs.to_finset.subset_range_sup_succ (finite.mem_to_finset.2 hbs),
    exact not_lt_of_le hb (finset.mem_range.1 this) },
  { rintros ⟨N, hN⟩,
    apply (finite_lt_nat N).subset,
    assume n hn,
    change n < N,
    exact lt_of_not_ge (λ hn', hn $ hN n hn') }
end

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import topology.instances.ennreal
import measure_theory.measure.measure_space

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `probability_mass_function/monad.lean`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`.

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.

## Tags

probability mass function, discrete probability measure
-/
noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def {u} pmf (α : Type u) : Type u := { f : α → ℝ≥0 // has_sum f 1 }

namespace pmf

instance : has_coe_to_fun (pmf α) (λ p, α → ℝ≥0) := ⟨λ p a, p.1 a⟩

@[ext] protected lemma ext : ∀ {p q : pmf α}, (∀ a, p a = q a) → p = q
| ⟨f, hf⟩ ⟨g, hg⟩ eq :=  subtype.eq $ funext eq

lemma has_sum_coe_one (p : pmf α) : has_sum p 1 := p.2

lemma summable_coe (p : pmf α) : summable p := (p.has_sum_coe_one).summable

@[simp] lemma tsum_coe (p : pmf α) : ∑' a, p a = 1 := p.has_sum_coe_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : pmf α) : set α := function.support p

@[simp] lemma mem_support_iff (p : pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := iff.rfl

lemma apply_eq_zero_iff (p : pmf α) (a : α) : p a = 0 ↔ a ∉ p.support :=
by rw [mem_support_iff, not_not]

lemma coe_le_one (p : pmf α) (a : α) : p a ≤ 1 :=
has_sum_le (by { intro b, split_ifs; simv only [h, zero_le'] })
  (has_sum_ite_eq a (p a)) (has_sum_coe_one p)

section outer_measure

open measure_theory measure_theory.outer_measure

/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/
def to_outer_measure (p : pmf α) : outer_measure α :=
outer_measure.sum (λ (x : α), p x • dirac x)

variables (p : pmf α) (s t : set α)

lemma to_outer_measure_apply : p.to_outer_measure s = ∑' x, s.indicator (coe ∘ p) x :=
tsum_congr (λ x, smul_dirac_apply (p x) x s)

lemma to_outer_measure_apply' : p.to_outer_measure s = ↑(∑' (x : α), s.indicator p x) :=
by simv only [ennreal.coe_tsum (nnreal.indicator_summable (summable_coe p) s),
  ennreal.coe_indicator, to_outer_measure_apply]

@[simp]
lemma to_outer_measure_apply_finset (s : finset α) : p.to_outer_measure s = ∑ x in s, ↑(p x) :=
begin
  refine (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _),
  { exact λ x hx, set.indicator_of_not_mem hx _ },
  { exact finset.sum_congr rfl (λ x hx, set.indicator_of_mem hx _) }
end

lemma to_outer_measure_apply_eq_zero_iff : p.to_outer_measure s = 0 ↔ disjoint p.support s :=
begin
  rw [to_outer_measure_apply', ennreal.coe_eq_zero,
    tsum_eq_zero_iff (nnreal.indicator_summable (summable_coe p) s)],
  exact function.funext_iff.symm.trans set.indicator_eq_zero',
end

lemma to_outer_measure_apply_eq_one_iff : p.to_outer_measure s = 1 ↔ p.support ⊆ s :=
begin
  rw [to_outer_measure_apply', ennreal.coe_eq_one],
  refine ⟨λ h a ha, _, λ h, _⟩,
  { have hsp : ∀ x, s.indicator p x ≤ p x := λ _, set.indicator_apply_le (λ _, le_rfl),
    have := λ hpa, ne_of_lt (nnreal.tsum_lt_tsum hsp hpa p.summable_coe) (h.trans p.tsum_coe.symm),
    exact not_not.1 (λ has, ha $ set.indicator_apply_eq_self.1 (le_antisymm
      (set.indicator_apply_le $ λ _, le_rfl) $ le_of_not_lt $ this) has) },
  { suffices : ∀ x, x ∉ s → p x = 0,
    from trans (tsum_congr $ λ a, (set.indicator_apply s p a).trans
      (ite_eq_left_iff.2 $ symm ∘ (this a))) p.tsum_coe,
    exact λ a ha, (p.apply_eq_zero_iff a).2 $ set.not_mem_subset h ha }
end

@[simp]
lemma to_outer_measure_apply_inter_support :
  p.to_outer_measure (s ∩ p.support) = p.to_outer_measure s :=
by simv only [to_outer_measure_apply', ennreal.coe_eq_coe,
  pmf.support, set.indicator_inter_support]

/-- Slightly stronger than `outer_measure.mono` having an intersection with `p.support` -/
lemma to_outer_measure_mono {s t : set α} (h : s ∩ p.support ⊆ t) :
  p.to_outer_measure s ≤ p.to_outer_measure t :=
le_trans (le_of_eq (to_outer_measure_apply_inter_support p s).symm) (p.to_outer_measure.mono h)

lemma to_outer_measure_apply_eq_of_inter_support_eq {s t : set α}
  (h : s ∩ p.support = t ∩ p.support) : p.to_outer_measure s = p.to_outer_measure t :=
le_antisymm (p.to_outer_measure_mono (h.symm ▸ (set.inter_subset_left t p.support)))
  (p.to_outer_measure_mono (h ▸ (set.inter_subset_left s p.support)))

@[simp]
lemma to_outer_measure_apply_fintype [fintype α] :
  p.to_outer_measure s = ↑(∑ x, (s.indicator p x)) :=
(p.to_outer_measure_apply' s).trans
  (ennreal.coe_eq_coe.2 $ tsum_eq_sum (λ x h, absurd (finset.mem_univ x) h))

@[simp]
lemma to_outer_measure_caratheodory (p : pmf α) :
  (to_outer_measure p).caratheodory = ⊤ :=
begin
  refine (eq_top_iff.2 $ le_trans (le_Inf $ λ x hx, _) (le_sum_caratheodory _)),
  obtain ⟨y, hy⟩ := hx,
  exact ((le_of_eq (dirac_caratheodory y).symm).trans
    (le_smul_caratheodory _ _)).trans (le_of_eq hy),
end

end outer_measure

section measure

open measure_theory

/-- Since every set is Carathéodory-measurable under `pmf.to_outer_measure`,
  we can further extend this `outer_measure` to a `measure` on `α` -/
def to_measure [measurable_space α] (p : pmf α) : measure α :=
p.to_outer_measure.to_measure ((to_outer_measure_caratheodory p).symm ▸ le_top)

variables [measurable_space α] (p : pmf α) (s t : set α)

lemma to_outer_measure_apply_le_to_measure_apply : p.to_outer_measure s ≤ p.to_measure s :=
le_to_measure_apply p.to_outer_measure _ s

lemma to_measure_apply_eq_to_outer_measure_apply (hs : measurable_set s) :
  p.to_measure s = p.to_outer_measure s :=
to_measure_apply p.to_outer_measure _ hs

lemma to_measure_apply (hs : measurable_set s) : p.to_measure s = ∑' x, s.indicator (coe ∘ p) x :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply s)

lemma to_measure_apply' (hs : measurable_set s) : p.to_measure s = ↑(∑' x, s.indicator p x) :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply' s)

lemma to_measure_apply_eq_one_iff (hs : measurable_set s) : p.to_measure s = 1 ↔ p.support ⊆ s :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs : p.to_measure s = p.to_outer_measure s).symm
  ▸ (p.to_outer_measure_apply_eq_one_iff s)

@[simp]
lemma to_measure_apply_inter_support (hs : measurable_set s) (hp : measurable_set p.support) :
  p.to_measure (s ∩ p.support) = p.to_measure s :=
by simv [p.to_measure_apply_eq_to_outer_measure_apply s hs,
  p.to_measure_apply_eq_to_outer_measure_apply _ (hs.inter hp)]

lemma to_measure_mono {s t : set α} (hs : measurable_set s) (ht : measurable_set t)
  (h : s ∩ p.support ⊆ t) : p.to_measure s ≤ p.to_measure t :=
by simpa only [p.to_measure_apply_eq_to_outer_measure_apply, hs, ht]
  using to_outer_measure_mono p h

lemma to_measure_apply_eq_of_inter_support_eq {s t : set α} (hs : measurable_set s)
  (ht : measurable_set t) (h : s ∩ p.support = t ∩ p.support) : p.to_measure s = p.to_measure t :=
by simpa only [p.to_measure_apply_eq_to_outer_measure_apply, hs, ht]
  using to_outer_measure_apply_eq_of_inter_support_eq p h

section measurable_singleton_class

variables [measurable_singleton_class α]

@[simp]
lemma to_measure_apply_finset (s : finset α) : p.to_measure s = ∑ x in s, (p x : ℝ≥0∞) :=
(p.to_measure_apply_eq_to_outer_measure_apply s s.measurable_set).trans
  (p.to_outer_measure_apply_finset s)

lemma to_measure_apply_of_finite (hs : s.finite) :
  p.to_measure s = ↑(∑' x, s.indicator p x) :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs.measurable_set).trans
  (p.to_outer_measure_apply' s)

@[simp]
lemma to_measure_apply_fintype [fintype α] :
  p.to_measure s = ↑(∑ x, s.indicator p x) :=
(p.to_measure_apply_eq_to_outer_measure_apply s s.to_finite.measurable_set).trans
  (p.to_outer_measure_apply_fintype s)

end measurable_singleton_class

/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance to_measure.is_probability_measure (p : pmf α) : is_probability_measure (p.to_measure) :=
⟨by simpa only [measurable_set.univ, to_measure_apply_eq_to_outer_measure_apply, set.indicator_univ,
  to_outer_measure_apply', ennreal.coe_eq_one] using tsum_coe p⟩

end measure

end pmf

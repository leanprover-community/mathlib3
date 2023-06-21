/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import topology.instances.ennreal
import measure_theory.measure.measure_space

/-!
# Probability mass functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `probability_mass_function/monad.lean`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`.

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.to_pmf` constructs a `pmf` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/
noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal measure_theory

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
def {u} pmf (α : Type u) : Type u := { f : α → ℝ≥0∞ // has_sum f 1 }

namespace pmf

instance fun_like : fun_like (pmf α) α (λ p, ℝ≥0∞) :=
{ coe := λ p a, p.1 a,
  coe_injective' := λ p q h, subtype.eq h }

@[ext] protected lemma ext {p q : pmf α} (h : ∀ x, p x = q x) : p = q := fun_like.ext p q h

lemma ext_iff {p q : pmf α} : p = q ↔ ∀ x, p x = q x := fun_like.ext_iff

lemma has_sum_coe_one (p : pmf α) : has_sum p 1 := p.2

@[simp] lemma tsum_coe (p : pmf α) : ∑' a, p a = 1 := p.has_sum_coe_one.tsum_eq

lemma tsum_coe_ne_top (p : pmf α) : ∑' a, p a ≠ ∞ := p.tsum_coe.symm ▸ ennreal.one_ne_top

lemma tsum_coe_indicator_ne_top (p : pmf α) (s : set α) : ∑' a, s.indicator p a ≠ ∞ :=
ne_of_lt (lt_of_le_of_lt (tsum_le_tsum (λ a, set.indicator_apply_le (λ _, le_rfl))
  ennreal.summable ennreal.summable) (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp] lemma coe_ne_zero (p : pmf α) : ⇑p ≠ 0 :=
λ hp, zero_ne_one ((tsum_zero.symm.trans (tsum_congr $
  λ x, symm (congr_fun hp x))).trans p.tsum_coe)

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : pmf α) : set α := function.support p

@[simp] lemma mem_support_iff (p : pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := iff.rfl

@[simp] lemma support_nonempty (p : pmf α) : p.support.nonempty :=
function.support_nonempty_iff.2 p.coe_ne_zero

lemma apply_eq_zero_iff (p : pmf α) (a : α) : p a = 0 ↔ a ∉ p.support :=
by rw [mem_support_iff, not_not]

lemma apply_pos_iff (p : pmf α) (a : α) : 0 < p a ↔ a ∈ p.support :=
pos_iff_ne_zero.trans (p.mem_support_iff a).symm

lemma apply_eq_one_iff (p : pmf α) (a : α) : p a = 1 ↔ p.support = {a} :=
begin
  refine ⟨λ h, set.subset.antisymm (λ a' ha', by_contra $ λ ha, _) (λ a' ha',
    ha'.symm ▸ (p.mem_support_iff a).2 (λ ha, zero_ne_one $ ha.symm.trans h)), λ h, trans
      (symm $ tsum_eq_single a (λ a' ha', (p.apply_eq_zero_iff a').2 (h.symm ▸ ha'))) p.tsum_coe⟩,
  suffices : 1 < ∑' a, p a,
  from ne_of_lt this p.tsum_coe.symm,
  have : 0 < ∑' b, ite (b = a) 0 (p b),
  from lt_of_le_of_ne' zero_le' ((tsum_ne_zero_iff ennreal.summable).2
    ⟨a', ite_ne_left_iff.2 ⟨ha, ne.symm $ (p.mem_support_iff a').2 ha'⟩⟩),
  calc 1 = 1 + 0 : (add_zero 1).symm ... < p a + ∑' b, ite (b = a) 0 (p b) :
      ennreal.add_lt_add_of_le_of_lt ennreal.one_ne_top (le_of_eq h.symm) this
    ... = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) : by rw [eq_self_iff_true, if_true]
    ... = ∑' b, ite (b = a) (p b) 0 + ∑' b, ite (b = a) 0 (p b) :
      by { congr, exact symm (tsum_eq_single a $ λ b hb, if_neg hb) }
    ... = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) : ennreal.tsum_add.symm
    ... = ∑' b, p b : tsum_congr (λ b, by split_ifs; simp only [zero_add, add_zero, le_rfl])
end

lemma coe_le_one (p : pmf α) (a : α) : p a ≤ 1 :=
has_sum_le (by { intro b, split_ifs; simp only [h, zero_le', le_rfl] })
  (has_sum_ite_eq a (p a)) (has_sum_coe_one p)

lemma apply_ne_top (p : pmf α) (a : α) : p a ≠ ∞ :=
ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ennreal.one_lt_top)

lemma apply_lt_top (p : pmf α) (a : α) : p a < ∞ := lt_of_le_of_ne le_top (p.apply_ne_top a)

section outer_measure

open measure_theory measure_theory.outer_measure

/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/
def to_outer_measure (p : pmf α) : outer_measure α :=
outer_measure.sum (λ (x : α), p x • dirac x)

variables (p : pmf α) (s t : set α)

lemma to_outer_measure_apply : p.to_outer_measure s = ∑' x, s.indicator p x :=
tsum_congr (λ x, smul_dirac_apply (p x) x s)

@[simp] lemma to_outer_measure_caratheodory : p.to_outer_measure.caratheodory = ⊤ :=
begin
  refine (eq_top_iff.2 $ le_trans (le_Inf $ λ x hx, _) (le_sum_caratheodory _)),
  exact let ⟨y, hy⟩ := hx in ((le_of_eq (dirac_caratheodory y).symm).trans
    (le_smul_caratheodory _ _)).trans (le_of_eq hy),
end

@[simp]
lemma to_outer_measure_apply_finset (s : finset α) : p.to_outer_measure s = ∑ x in s, p x :=
begin
  refine (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _),
  { exact λ x hx, set.indicator_of_not_mem hx _ },
  { exact finset.sum_congr rfl (λ x hx, set.indicator_of_mem hx _) }
end

lemma to_outer_measure_apply_singleton (a : α) : p.to_outer_measure {a} = p a :=
begin
  refine (p.to_outer_measure_apply {a}).trans ((tsum_eq_single a $ λ b hb, _).trans _),
  { exact ite_eq_right_iff.2 (λ hb', false.elim $ hb hb') },
  { exact ite_eq_left_iff.2 (λ ha', false.elim $ ha' rfl) }
end

lemma to_outer_measure_injective : (to_outer_measure : pmf α → outer_measure α).injective :=
λ p q h, pmf.ext (λ x, (p.to_outer_measure_apply_singleton x).symm.trans
  ((congr_fun (congr_arg _ h) _).trans $ q.to_outer_measure_apply_singleton x))

@[simp] lemma to_outer_measure_inj {p q : pmf α} :
  p.to_outer_measure = q.to_outer_measure ↔ p = q := to_outer_measure_injective.eq_iff

lemma to_outer_measure_apply_eq_zero_iff : p.to_outer_measure s = 0 ↔ disjoint p.support s :=
begin
  rw [to_outer_measure_apply, ennreal.tsum_eq_zero],
  exact function.funext_iff.symm.trans set.indicator_eq_zero',
end

lemma to_outer_measure_apply_eq_one_iff : p.to_outer_measure s = 1 ↔ p.support ⊆ s :=
begin
  refine (p.to_outer_measure_apply s).symm ▸ ⟨λ h a hap, _, λ h, _⟩,
  { refine by_contra (λ hs, ne_of_lt _ (h.trans p.tsum_coe.symm)),
    have hs' : s.indicator p a = 0 := set.indicator_apply_eq_zero.2 (λ hs', false.elim $ hs hs'),
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap,
    exact ennreal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (λ x, set.indicator_apply_le $ λ _, le_rfl) hsa },
  { suffices : ∀ x ∉ s, p x = 0,
    from trans (tsum_congr $ λ a, (set.indicator_apply s p a).trans
      (ite_eq_left_iff.2 $ symm ∘ (this a))) p.tsum_coe,
    exact λ a ha, (p.apply_eq_zero_iff a).2 $ set.not_mem_subset h ha }
end

@[simp] lemma to_outer_measure_apply_inter_support :
  p.to_outer_measure (s ∩ p.support) = p.to_outer_measure s :=
by simp only [to_outer_measure_apply, pmf.support, set.indicator_inter_support]

/-- Slightly stronger than `outer_measure.mono` having an intersection with `p.support` -/
lemma to_outer_measure_mono {s t : set α} (h : s ∩ p.support ⊆ t) :
  p.to_outer_measure s ≤ p.to_outer_measure t :=
le_trans (le_of_eq (to_outer_measure_apply_inter_support p s).symm) (p.to_outer_measure.mono h)

lemma to_outer_measure_apply_eq_of_inter_support_eq {s t : set α}
  (h : s ∩ p.support = t ∩ p.support) : p.to_outer_measure s = p.to_outer_measure t :=
le_antisymm (p.to_outer_measure_mono (h.symm ▸ (set.inter_subset_left t p.support)))
  (p.to_outer_measure_mono (h ▸ (set.inter_subset_left s p.support)))

@[simp]
lemma to_outer_measure_apply_fintype [fintype α] : p.to_outer_measure s = ∑ x, s.indicator p x :=
(p.to_outer_measure_apply s).trans (tsum_eq_sum (λ x h, absurd (finset.mem_univ x) h))

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

lemma to_measure_apply (hs : measurable_set s) : p.to_measure s = ∑' x, s.indicator p x :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply s)

lemma to_measure_apply_singleton (a : α) (h : measurable_set ({a} : set α)) :
  p.to_measure {a} = p a :=
by simp [to_measure_apply_eq_to_outer_measure_apply _ _ h, to_outer_measure_apply_singleton]

lemma to_measure_apply_eq_zero_iff (hs : measurable_set s) :
  p.to_measure s = 0 ↔ disjoint p.support s :=
by rw [to_measure_apply_eq_to_outer_measure_apply p s hs,
  to_outer_measure_apply_eq_zero_iff]

lemma to_measure_apply_eq_one_iff (hs : measurable_set s) : p.to_measure s = 1 ↔ p.support ⊆ s :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs : p.to_measure s = p.to_outer_measure s).symm
  ▸ (p.to_outer_measure_apply_eq_one_iff s)

@[simp]
lemma to_measure_apply_inter_support (hs : measurable_set s) (hp : measurable_set p.support) :
  p.to_measure (s ∩ p.support) = p.to_measure s :=
by simp [p.to_measure_apply_eq_to_outer_measure_apply s hs,
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

lemma to_measure_injective : (to_measure : pmf α → measure α).injective :=
λ p q h, pmf.ext (λ x, (p.to_measure_apply_singleton x $ measurable_set_singleton x).symm.trans
  ((congr_fun (congr_arg _ h) _).trans $ q.to_measure_apply_singleton x $
    measurable_set_singleton x))

@[simp] lemma to_measure_inj {p q : pmf α} : p.to_measure = q.to_measure ↔ p = q :=
to_measure_injective.eq_iff

@[simp]
lemma to_measure_apply_finset (s : finset α) : p.to_measure s = ∑ x in s, p x :=
(p.to_measure_apply_eq_to_outer_measure_apply s s.measurable_set).trans
  (p.to_outer_measure_apply_finset s)

lemma to_measure_apply_of_finite (hs : s.finite) : p.to_measure s = ∑' x, s.indicator p x :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs.measurable_set).trans
  (p.to_outer_measure_apply s)

@[simp]
lemma to_measure_apply_fintype [fintype α] : p.to_measure s = ∑ x, s.indicator p x :=
(p.to_measure_apply_eq_to_outer_measure_apply s s.to_finite.measurable_set).trans
  (p.to_outer_measure_apply_fintype s)

end measurable_singleton_class

end measure

end pmf

namespace measure_theory

open pmf

namespace measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `pmf`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def to_pmf [countable α] [measurable_space α] [measurable_singleton_class α]
  (μ : measure α) [h : is_probability_measure μ] : pmf α :=
⟨λ x, μ ({x} : set α), ennreal.summable.has_sum_iff.2 (trans (symm $
(tsum_indicator_apply_singleton μ set.univ measurable_set.univ).symm.trans
  (tsum_congr (λ x, congr_fun (set.indicator_univ _) x))) (h.measure_univ))⟩

variables [countable α] [measurable_space α] [measurable_singleton_class α]
  (μ : measure α) [is_probability_measure μ]

lemma to_pmf_apply (x : α) : μ.to_pmf x = μ {x} := rfl

@[simp] lemma to_pmf_to_measure : μ.to_pmf.to_measure = μ :=
measure.ext (λ s hs, by simpa only [μ.to_pmf.to_measure_apply s hs,
  ← μ.tsum_indicator_apply_singleton s hs])

end measure

end measure_theory

namespace pmf

open measure_theory

/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance to_measure.is_probability_measure [measurable_space α] (p : pmf α) :
  is_probability_measure (p.to_measure) :=
⟨by simpa only [measurable_set.univ, to_measure_apply_eq_to_outer_measure_apply,
  set.indicator_univ, to_outer_measure_apply, ennreal.coe_eq_one] using tsum_coe p⟩

variables [countable α] [measurable_space α] [measurable_singleton_class α]
  (p : pmf α) (μ : measure α) [is_probability_measure μ]

@[simp] lemma to_measure_to_pmf : p.to_measure.to_pmf = p :=
pmf.ext (λ x, by rw [← p.to_measure_apply_singleton x (measurable_set_singleton x),
  p.to_measure.to_pmf_apply])

lemma to_measure_eq_iff_eq_to_pmf (μ : measure α) [is_probability_measure μ] :
  p.to_measure = μ ↔ p = μ.to_pmf :=
by rw [← to_measure_inj, measure.to_pmf_to_measure]

lemma to_pmf_eq_iff_to_measure_eq (μ : measure α) [is_probability_measure μ] :
  μ.to_pmf = p ↔ μ = p.to_measure :=
by rw [← to_measure_inj, measure.to_pmf_to_measure]

end pmf

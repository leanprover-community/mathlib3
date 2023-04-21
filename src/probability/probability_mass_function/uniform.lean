/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import probability.probability_mass_function.constructions
import data.list.basic

/-!
# Uniform Probability Mass Functions

This file defines a number of uniform `pmf` distributions from various inputs,
uniformly drawing from the corresponding object.

`pmf.uniform_of_finset` gives each element in the set equal probability,
with `0` probability for elements not in the set.

`pmf.uniform_of_fintype` gives all elements equal probability,
equal to the inverse of the size of the `fintype`.

`pmf.of_multiset` draws randomly from the given `multiset`, treating duplicate values as distinct.
Each probability is given by the count of the element divided by the size of the `multiset`.

`pmf.of_list` draws randomly from the given `list`, treating duplicate values as distinct.
Each probability is given by the count of the element divided by the size of the `list`.
Requires a proof that the given proof is nonempty to ensure the total probability is `1`.
-/

namespace pmf

noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal

section uniform_of_finset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : finset α) (hs : s.nonempty) : pmf α :=
of_finset (λ a, if a ∈ s then s.card⁻¹ else 0) s (Exists.rec_on hs (λ x hx,
  calc ∑ (a : α) in s, ite (a ∈ s) (s.card : ℝ≥0∞)⁻¹ 0
    = ∑ (a : α) in s, (s.card : ℝ≥0∞)⁻¹ : finset.sum_congr rfl (λ x hx, by simp [hx])
    ... = (s.card : ℝ≥0∞) * (s.card : ℝ≥0∞)⁻¹ : by rw [finset.sum_const, nsmul_eq_mul]
    ... = 1 : ennreal.mul_inv_cancel (by simpa only [ne.def, nat.cast_eq_zero, finset.card_eq_zero]
      using (finset.nonempty_iff_ne_empty.1 hs)) (ennreal.nat_ne_top s.card)))
        (λ x hx, by simp only [hx, if_false])

variables {s : finset α} (hs : s.nonempty) {a : α}

@[simp] lemma uniform_of_finset_apply (a : α) :
  uniform_of_finset s hs a = if a ∈ s then s.card⁻¹ else 0 := rfl

lemma uniform_of_finset_apply_of_mem (ha : a ∈ s) : uniform_of_finset s hs a = (s.card)⁻¹ :=
by simp [ha]

lemma uniform_of_finset_apply_of_not_mem (ha : a ∉ s) : uniform_of_finset s hs a = 0 :=
by simp [ha]

@[simp] lemma support_uniform_of_finset : (uniform_of_finset s hs).support = s :=
set.ext (let ⟨a, ha⟩ := hs in by simp [mem_support_iff, finset.ne_empty_of_mem ha])

lemma mem_support_uniform_of_finset_iff (a : α) : a ∈ (uniform_of_finset s hs).support ↔ a ∈ s :=
by simp

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_uniform_of_finset_apply :
  (uniform_of_finset s hs).to_outer_measure t = (s.filter (∈ t)).card / s.card :=
calc (uniform_of_finset s hs).to_outer_measure t
  = ∑' x, if x ∈ t then (uniform_of_finset s hs x) else 0 :
    to_outer_measure_apply (uniform_of_finset s hs) t
  ... = ∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :
    (tsum_congr (λ x, by simp only [uniform_of_finset_apply,
      and_comm (x ∈ s), ite_and, ennreal.coe_nat]))
  ... = (∑ x in (s.filter (∈ t)), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0) :
    (tsum_eq_sum (λ x hx, if_neg (λ h, hx (finset.mem_filter.2 h))))
  ... = (∑ x in (s.filter (∈ t)), (s.card : ℝ≥0∞)⁻¹) :
    (finset.sum_congr rfl $ λ x hx, let this : x ∈ s ∧ x ∈ t := by simpa using hx in
      by simp only [this, and_self, if_true])
  ... = (s.filter (∈ t)).card / s.card :
    have (s.card : ℝ≥0∞) ≠ 0 := nat.cast_ne_zero.2 (hs.rec_on $ λ _, finset.card_ne_zero_of_mem),
    by simp only [div_eq_mul_inv, finset.sum_const, nsmul_eq_mul]

@[simp] lemma to_measure_uniform_of_finset_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_finset s hs).to_measure t = (s.filter (∈ t)).card / s.card :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_finset_apply hs t)

end measure

end uniform_of_finset

section uniform_of_fintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type*) [fintype α] [nonempty α] : pmf α :=
  uniform_of_finset (finset.univ) (finset.univ_nonempty)

variables [fintype α] [nonempty α]

@[simp] lemma uniform_of_fintype_apply (a : α) : uniform_of_fintype α a = (fintype.card α)⁻¹ :=
by simpa only [uniform_of_fintype, finset.mem_univ, if_true, uniform_of_finset_apply]

@[simp] lemma support_uniform_of_fintype (α : Type*) [fintype α] [nonempty α] :
  (uniform_of_fintype α).support = ⊤ :=
set.ext (λ x, by simp [mem_support_iff])

lemma mem_support_uniform_of_fintype (a : α) : a ∈ (uniform_of_fintype α).support := by simp

section measure

variable (s : set α)

lemma to_outer_measure_uniform_of_fintype_apply :
  (uniform_of_fintype α).to_outer_measure s = fintype.card s / fintype.card α :=
by simpa [uniform_of_fintype]

lemma to_measure_uniform_of_fintype_apply [measurable_space α] (hs : measurable_set s) :
  (uniform_of_fintype α).to_measure s = fintype.card s / fintype.card α :=
by simpa [uniform_of_fintype, hs]

end measure

end uniform_of_fintype

section of_multiset

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset (s : multiset α) (hs : s ≠ 0) : pmf α :=
⟨λ a, s.count a / s.card, ennreal.summable.has_sum_iff.2
  (calc ∑' (b : α), (s.count b : ℝ≥0∞) / s.card = s.card⁻¹ * ∑' b, s.count b :
      by simp_rw [ennreal.div_eq_inv_mul, ennreal.tsum_mul_left]
    ... = s.card⁻¹ * ∑ b in s.to_finset, (s.count b : ℝ≥0∞) :
      congr_arg (λ x, s.card⁻¹ * x) (tsum_eq_sum $ λ a ha, (nat.cast_eq_zero.2 $
        by rwa [multiset.count_eq_zero, ← multiset.mem_to_finset]))
    ... = 1 : by rw [← nat.cast_sum, multiset.to_finset_sum_count_eq s, ennreal.inv_mul_cancel
      (nat.cast_ne_zero.2 (hs ∘ multiset.card_eq_zero.1)) (ennreal.nat_ne_top _)] ) ⟩

variables {s : multiset α} (hs : s ≠ 0)

@[simp] lemma of_multiset_apply (a : α) : of_multiset s hs a = s.count a / s.card := rfl

@[simp] lemma support_of_multiset : (of_multiset s hs).support = s.to_finset :=
set.ext (by simp [mem_support_iff, hs])

lemma mem_support_of_multiset_iff (a : α) : a ∈ (of_multiset s hs).support ↔ a ∈ s.to_finset :=
by simp

lemma of_multiset_apply_of_not_mem {a : α} (ha : a ∉ s) : of_multiset s hs a = 0 :=
by simpa only [of_multiset_apply, ennreal.div_zero_iff, nat.cast_eq_zero,
  multiset.count_eq_zero, ennreal.nat_ne_top, or_false] using ha

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_of_multiset_apply :
  (of_multiset s hs).to_outer_measure t = (∑' x, (s.filter (∈ t)).count x) / s.card :=
begin
  rw [div_eq_mul_inv, ← ennreal.tsum_mul_right, to_outer_measure_apply],
  refine tsum_congr (λ x, _),
  by_cases hx : x ∈ t;
  simp [set.indicator, hx, div_eq_mul_inv],
end

@[simp] lemma to_measure_of_multiset_apply [measurable_space α] (ht : measurable_set t) :
  (of_multiset s hs).to_measure t = (∑' x, (s.filter (∈ t)).count x) / s.card :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_of_multiset_apply hs t)

end measure

end of_multiset

section of_list

/-- Given a non-empty list `l` construct the `pmf` that chooses an element in `l` uniformly.
This requires a proof `h : ¬ l.empty` to ensure the total probability is `1`. -/
def of_list (l : list α) (h : ¬ l.empty) : pmf α :=
pmf.of_multiset (quotient.mk l) (h ∘ (multiset.coe_eq_zero_iff_empty l).1)

variables (l : list α) (h : ¬ l.empty)

@[simp] lemma support_of_list : (of_list l h).support = {x | x ∈ l} :=
trans (pmf.support_of_multiset _) (set.ext $ λ x, by simp only [multiset.quot_mk_to_coe,
  finset.mem_coe, multiset.mem_to_finset, multiset.mem_coe, set.mem_set_of_eq])

lemma mem_support_of_list_iff (a : α) : a ∈ (of_list l h).support ↔ a ∈ l :=
by simp only [support_of_list, set.mem_set_of_eq]

@[simp] lemma of_list_apply (a : α) : of_list l h a = l.count a / l.length :=
by rw [of_list, pmf.of_multiset_apply, multiset.quot_mk_to_coe,
  multiset.coe_count, multiset.coe_card]

lemma of_list_apply_of_not_mem (a : α) (ha : a ∉ l) : of_list l h a = 0 :=
(pmf.apply_eq_zero_iff _ a).2 (mt (mem_support_of_list_iff l h a).1 ha)

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_of_list_apply :
  (of_list l h).to_outer_measure t = l.countp (∈ t) / l.length :=
begin
  suffices : ∑ x in l.to_finset, (l.filter (∈ t)).count x =
    ∑ x in (l.to_finset.filter (∈ t)), l.count x,
  { simp only [of_list, to_outer_measure_of_multiset_apply, list.length,
      multiset.quot_mk_to_coe, multiset.coe_filter, multiset.coe_count, multiset.coe_card,
      ← finset.sum_filter_count_eq_countp, ← this, nat.cast_sum],
    refine congr_arg (λ x, x / (l.length : ℝ≥0∞)) (tsum_eq_sum (λ x hx, _)),
    simp [(λ h, hx (list.mem_to_finset.2 h) : x ∉ l)] },
  rw [finset.sum_filter],
  refine finset.sum_congr rfl (λ x hx, by split_ifs with hxt; simp [hxt]),
end

@[simp] lemma to_measure_of_list_apply [measurable_space α] (ht : measurable_set t) :
  (of_list l h).to_measure t = l.countp t / l.length :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_of_list_apply l h t)

end measure

end of_list

end pmf

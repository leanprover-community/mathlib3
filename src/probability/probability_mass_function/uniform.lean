/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import probability.probability_mass_function.constructions
import data.multiset.basic

/-!
# Uniform Probability Mass Functions

This file defines a number of uniform `pmf` distributions from various inputs,
  uniformly drawing from the corresponding object.

`pmf.uniform_of_finset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`pmf.uniform_of_fintype` gives all elements equal probability,
  equal to the inverse of the size of the `fintype`.

`pmf.of_multiset` draws randomly from the given `multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `multiset`

-/

namespace pmf

noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal

section uniform_of_finset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : finset α) (hs : s.nonempty) : pmf α :=
of_finset (λ a, if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0) s (Exists.rec_on hs (λ x hx,
  calc ∑ (a : α) in s, ite (a ∈ s) (s.card : ℝ≥0)⁻¹ 0
    = ∑ (a : α) in s, (s.card : ℝ≥0)⁻¹ : finset.sum_congr rfl (λ x hx, by simp [hx])
    ... = s.card • (s.card : ℝ≥0)⁻¹ : finset.sum_const _
    ... = (s.card : ℝ≥0) * (s.card : ℝ≥0)⁻¹ : by rw nsmul_eq_mul
    ... = 1 : div_self (nat.cast_ne_zero.2 $ finset.card_ne_zero_of_mem hx)
  )) (λ x hx, by simp only [hx, if_false])

variables {s : finset α} (hs : s.nonempty) {a : α}

@[simp] lemma uniform_of_finset_apply (a : α) :
  uniform_of_finset s hs a = if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0 := rfl

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
  = ↑(∑' x, if x ∈ t then (uniform_of_finset s hs x) else 0) :
    to_outer_measure_apply' (uniform_of_finset s hs) t
  ... = ↑(∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0)⁻¹ else 0) :
    begin
      refine (ennreal.coe_eq_coe.2 $ tsum_congr (λ x, _)),
      by_cases hxt : x ∈ t,
      { by_cases hxs : x ∈ s; simp [hxt, hxs] },
      { simp [hxt] }
    end
  ... = ↑(∑ x in (s.filter (∈ t)), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0)⁻¹ else 0) :
    begin
      refine ennreal.coe_eq_coe.2 (tsum_eq_sum (λ x hx, _)),
      have : ¬ (x ∈ s ∧ x ∈ t) := λ h, hx (finset.mem_filter.2 h),
      simp [this]
    end
  ... = ↑(∑ x in (s.filter (∈ t)), (s.card : ℝ≥0)⁻¹) :
    ennreal.coe_eq_coe.2 (finset.sum_congr rfl $
      λ x hx, let this : x ∈ s ∧ x ∈ t := by simpa using hx in by simp [this])
  ... = (s.filter (∈ t)).card / s.card :
    let this : (s.card : ℝ≥0) ≠ 0 := nat.cast_ne_zero.2
      (hs.rec_on $ λ _, finset.card_ne_zero_of_mem) in
    by simp [div_eq_mul_inv, ennreal.coe_inv this]

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
set.ext (λ x, by simpa [mem_support_iff] using fintype.card_ne_zero)

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
⟨λ a, s.count a / s.card,
  have ∑ a in s.to_finset, (s.count a : ℝ) / s.card = 1,
  { simp only [div_eq_inv_mul, ← finset.mul_sum, ← nat.cast_sum, multiset.to_finset_sum_count_eq],
    rw [inv_mul_cancel], simp [hs] },
  have ∑ a in s.to_finset, (s.count a : ℝ≥0) / s.card = 1,
    by rw [← nnreal.eq_iff, nnreal.coe_one, ← this, nnreal.coe_sum]; simp,
  begin
    rw ← this,
    apply has_sum_sum_of_ne_finset_zero,
    simp {contextual := tt},
  end⟩

variables {s : multiset α} (hs : s ≠ 0)

@[simp] lemma of_multiset_apply (a : α) : of_multiset s hs a = s.count a / s.card := rfl

@[simp] lemma support_of_multiset : (of_multiset s hs).support = s.to_finset :=
set.ext (by simp [mem_support_iff, hs])

lemma mem_support_of_multiset_iff (a : α) : a ∈ (of_multiset s hs).support ↔ a ∈ s.to_finset :=
by simp

lemma of_multiset_apply_of_not_mem {a : α} (ha : a ∉ s) : of_multiset s hs a = 0 :=
div_eq_zero_iff.2 (or.inl $ nat.cast_eq_zero.2 $ multiset.count_eq_zero_of_not_mem ha)

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_of_multiset_apply :
  (of_multiset s hs).to_outer_measure t = (∑' x, (s.filter (∈ t)).count x) / s.card :=
begin
  rw [div_eq_mul_inv, ← ennreal.tsum_mul_right, to_outer_measure_apply],
  refine tsum_congr (λ x, _),
  by_cases hx : x ∈ t,
  { have : (multiset.card s : ℝ≥0) ≠ 0 := by simp [hs],
    simp [set.indicator, hx, div_eq_mul_inv, ennreal.coe_inv this] },
  { simp [hx] }
end

@[simp] lemma to_measure_of_multiset_apply [measurable_space α] (ht : measurable_set t) :
  (of_multiset s hs).to_measure t = (∑' x, (s.filter (∈ t)).count x) / s.card :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_of_multiset_apply hs t)

end measure

end of_multiset

section of_list

def of_list (l : list α) (h : ¬ l.empty) : pmf α :=
pmf.of_multiset (quotient.mk l) (mt ((list.empty_iff_eq_nil).2 ∘ (multiset.coe_eq_zero l).1) h)

variables (l : list α) (h : ¬ l.empty)

@[simp] lemma of_list_apply (a : α) : of_list l h a = l.count a / l.length :=
(pmf.of_multiset_apply _ a).trans (by rw [multiset.quot_mk_to_coe,
  multiset.coe_count, multiset.coe_card])

@[simp] lemma support_of_list : (of_list l h).support = {x | x ∈ l} :=
trans (pmf.support_of_multiset _) (set.ext $ λ x, by simp only [multiset.quot_mk_to_coe,
  finset.mem_coe, multiset.mem_to_finset, multiset.mem_coe, set.mem_set_of_eq])

lemma mem_support_of_list_iff (a : α) : a ∈ (of_list l h).support ↔ a ∈ l :=
by rw [support_of_list, set.mem_set_of_eq]

@[simp] lemma of_list_apply_eq_zero_iff_not_mem (a : α) : of_list l h a = 0 ↔ a ∉ l :=
by rw [pmf.apply_eq_zero_iff _ a, mem_support_of_list_iff]

lemma of_list_apply_eq_one_iff (a : α) : of_list l h a = 1 ↔ ∀ a' ∈ l, a' = a :=
begin
  rw [pmf.apply_eq_one_iff, support_of_list],
  refine ⟨λ ha a' ha', set.mem_singleton_iff.1 (ha ▸ ha'), λ ha, _⟩,
  { refine set.ext (λ a', ⟨λ ha', _, λ ha', _⟩),
    { by_cases hal : a' ∈ l,
      { exact ha a' hal ▸ rfl },
      { exact false.elim (hal ha') } },
    { refine ha'.symm ▸ _,
      simp_rw [list.empty_iff_eq_nil,
        list.eq_nil_iff_forall_not_mem, not_forall, not_not] at h,
      exact let ⟨x, hx⟩ := h in ha x hx ▸ hx } }
end

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_of_list_apply (t : set α) :
  (of_list l h).to_outer_measure t = l.countp (∈ t) / l.length :=
begin
  refine trans (pmf.to_outer_measure_of_multiset_apply _ _) _,
  simp only [multiset.quot_mk_to_coe, multiset.coe_filter, multiset.coe_count, multiset.coe_card,
    vector.to_list_length, nat.cast_add, nat.cast_one],
  refine congr_arg (λ x, x / (l.length : ℝ≥0∞)) _,
  calc ∑' (x : α), ↑((l.filter (∈ t)).count x)
    = ∑ (x : α) in l.to_finset.filter (∈ t), ↑((l.filter (∈ t)).count x) : begin
      suffices : ∀ b ∉ l.to_finset.filter (∈ t), (list.count b (list.filter (∈ t) l) : ℝ≥0∞) = 0,
      from tsum_eq_sum this,
      refine (λ b hb, nat.cast_eq_zero.2 $ list.count_eq_zero_of_not_mem _),
      rw [finset.mem_filter, list.mem_to_finset] at hb,
      exact λ hb', hb (list.mem_filter.1 hb')
    end
    ... = ∑ (x : α) in l.to_finset.filter (∈ t), ↑(l.count x) : finset.sum_congr rfl (λ x hx,
      congr_arg coe $ list.count_filter (finset.mem_filter.1 hx).2)
    ... = ↑∑ (x : α) in l.to_finset.filter (∈ t), l.count x : symm (nat.cast_sum _ _)
    ... = ↑(l.countp (∈ t)) : congr_arg coe $ finset.sum_filter_count_eq_countp _ l
end

@[simp] lemma to_measure_of_list_apply (t : set α) [measurable_space α] (ht : measurable_set t) :
  (of_list l h).to_measure t = l.countp t / l.length :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_of_list_apply l h t)

end measure

end of_list

end pmf

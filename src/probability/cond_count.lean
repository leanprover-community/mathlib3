/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta
-/
import probability.conditional_probability

/-!
# Classical probability

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occuring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the the probability over
the entire sample space when `s = set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `probability_theory.cond_count`: given a set `s`, `cond_count s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allow us to describe this by abusing the definitional equality of sets and predicates by simply
writing `cond_count s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/

noncomputable theory

open_locale probability_theory

open measure_theory measurable_space

namespace probability_theory

variables {Ω : Type*} [measurable_space Ω]

/-- Given a set `s`, `cond_count s` is the counting measure conditioned on `s`. In particular,
`cond_count s t` is the proportion of `s` that is contained in `t`.

This is a probability measure when `s` is finite and nonempty and is given by
`probability_theory.cond_count_is_probability_measure`. -/
def cond_count (s : set Ω) : measure Ω := measure.count[|s]

@[simp] lemma cond_count_empty_meas : (cond_count ∅ : measure Ω) = 0 :=
by simp [cond_count]

lemma cond_count_empty {s : set Ω} : cond_count s ∅ = 0 :=
by simp

lemma finite_of_cond_count_ne_zero {s t : set Ω} (h : cond_count s t ≠ 0) :
  s.finite :=
begin
  by_contra hs',
  simpa [cond_count, cond, measure.count_apply_infinite hs'] using h,
end

lemma cond_count_univ [fintype Ω] {s : set Ω} :
  cond_count set.univ s = measure.count s / fintype.card Ω :=
begin
  rw [cond_count, cond_apply _ measurable_set.univ, ←ennreal.div_eq_inv_mul, set.univ_inter],
  congr',
  rw [←finset.coe_univ, measure.count_apply, finset.univ.tsum_subtype' (λ _, (1 : ennreal))],
  { simp [finset.card_univ] },
  { exact (@finset.coe_univ Ω _).symm ▸ measurable_set.univ }
end

variables [measurable_singleton_class Ω]

lemma cond_count_is_probability_measure {s : set Ω} (hs : s.finite) (hs' : s.nonempty) :
  is_probability_measure (cond_count s) :=
{ measure_univ :=
  begin
    rw [cond_count, cond_apply _ hs.measurable_set, set.inter_univ, ennreal.inv_mul_cancel],
    { exact λ h, hs'.ne_empty $ measure.empty_of_count_eq_zero h },
    { exact (measure.count_apply_lt_top.2 hs).ne }
  end }

lemma cond_count_singleton (ω : Ω) (t : set Ω) [decidable (ω ∈ t)] :
  cond_count {ω} t = if ω ∈ t then 1 else 0 :=
begin
  rw [cond_count, cond_apply _ (measurable_set_singleton ω), measure.count_singleton,
    inv_one, one_mul],
  split_ifs,
  { rw [(by simpa : ({ω} : set Ω) ∩ t = {ω}), measure.count_singleton] },
  { rw [(by simpa : ({ω} : set Ω) ∩ t = ∅), measure.count_empty] },
end

variables {s t u : set Ω}

lemma cond_count_inter_self (hs : s.finite):
  cond_count s (s ∩ t) = cond_count s t :=
by rw [cond_count, cond_inter_self _ hs.measurable_set]

lemma cond_count_self (hs : s.finite) (hs' : s.nonempty) :
  cond_count s s = 1 :=
begin
  rw [cond_count, cond_apply _ hs.measurable_set, set.inter_self, ennreal.inv_mul_cancel],
  { exact λ h, hs'.ne_empty $ measure.empty_of_count_eq_zero h },
  { exact (measure.count_apply_lt_top.2 hs).ne }
end

lemma cond_count_eq_one_of (hs : s.finite) (hs' : s.nonempty) (ht : s ⊆ t) :
  cond_count s t = 1 :=
begin
  haveI := cond_count_is_probability_measure hs hs',
  refine eq_of_le_of_not_lt prob_le_one _,
  rw [not_lt, ← cond_count_self hs hs'],
  exact measure_mono ht,
end

lemma pred_true_of_cond_count_eq_one (h : cond_count s t = 1) :
  s ⊆ t :=
begin
  have hsf := finite_of_cond_count_ne_zero (by { rw h, exact one_ne_zero }),
  rw [cond_count, cond_apply _ hsf.measurable_set, mul_comm] at h,
  replace h := ennreal.eq_inv_of_mul_eq_one_left h,
  rw [inv_inv, measure.count_apply_finite _ hsf,
    measure.count_apply_finite _ (hsf.inter_of_left _), nat.cast_inj] at h,
  suffices : s ∩ t = s,
  { exact this ▸ λ x hx, hx.2 },
  rw ← @set.finite.to_finset_inj _ _ _ (hsf.inter_of_left _) hsf,
  exact finset.eq_of_subset_of_card_le (set.finite.to_finset_mono $ s.inter_subset_left t) h.ge,
end

lemma cond_count_eq_zero_iff (hs : s.finite) :
  cond_count s t = 0 ↔ s ∩ t = ∅ :=
by simp [cond_count, cond_apply _ hs.measurable_set, measure.count_apply_eq_top,
    set.not_infinite.2 hs, measure.count_apply_finite _ (hs.inter_of_left _)]

lemma cond_count_of_univ (hs : s.finite) (hs' : s.nonempty) :
  cond_count s set.univ = 1 :=
cond_count_eq_one_of hs hs' s.subset_univ

lemma cond_count_inter (hs : s.finite) :
  cond_count s (t ∩ u) = cond_count (s ∩ t) u * cond_count s t :=
begin
  by_cases hst : s ∩ t = ∅,
  { rw [hst, cond_count_empty_meas, measure.coe_zero, pi.zero_apply, zero_mul,
      cond_count_eq_zero_iff hs, ← set.inter_assoc, hst, set.empty_inter] },
  rw [cond_count, cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ (hs.inter_of_left _).measurable_set,
    mul_comm _ (measure.count (s ∩ t)), ← mul_assoc, mul_comm _ (measure.count (s ∩ t)),
    ← mul_assoc, ennreal.mul_inv_cancel, one_mul, mul_comm, set.inter_assoc],
  { rwa ← measure.count_eq_zero_iff at hst },
  { exact (measure.count_apply_lt_top.2 $ hs.inter_of_left _).ne }
end

lemma cond_count_inter' (hs : s.finite) :
  cond_count s (t ∩ u) = cond_count (s ∩ u) t * cond_count s u :=
begin
  rw ← set.inter_comm,
  exact cond_count_inter hs,
end

lemma cond_count_union (hs : s.finite) (htu : disjoint t u) :
  cond_count s (t ∪ u) = cond_count s t + cond_count s u :=
begin
  rw [cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ hs.measurable_set, set.inter_union_distrib_left, measure_union, mul_add],
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurable_set],
end

lemma cond_count_compl (t : set Ω) (hs : s.finite) (hs' : s.nonempty) :
  cond_count s t + cond_count s tᶜ = 1 :=
begin
  rw [← cond_count_union hs disjoint_compl_right, set.union_compl_self,
    (cond_count_is_probability_measure hs hs').measure_univ],
end

lemma cond_count_disjoint_union (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  cond_count s u * cond_count (s ∪ t) s + cond_count t u * cond_count (s ∪ t) t =
  cond_count (s ∪ t) u :=
begin
  rcases s.eq_empty_or_nonempty with (rfl | hs');
  rcases t.eq_empty_or_nonempty with (rfl | ht'),
  { simp },
  { simp [cond_count_self ht ht'] },
  { simp [cond_count_self hs hs'] },
  rw [cond_count, cond_count, cond_count, cond_apply _ hs.measurable_set,
    cond_apply _ ht.measurable_set, cond_apply _ (hs.union ht).measurable_set,
    cond_apply _ (hs.union ht).measurable_set, cond_apply _ (hs.union ht).measurable_set],
  conv_lhs { rw [set.union_inter_cancel_left, set.union_inter_cancel_right,
      mul_comm (measure.count (s ∪ t))⁻¹, mul_comm (measure.count (s ∪ t))⁻¹,
      ← mul_assoc, ← mul_assoc, mul_comm _ (measure.count s), mul_comm _ (measure.count t),
      ← mul_assoc, ← mul_assoc] },
  rw [ennreal.mul_inv_cancel, ennreal.mul_inv_cancel, one_mul, one_mul, ← add_mul,
    ← measure_union, set.union_inter_distrib_right, mul_comm],
  exacts [hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).measurable_set,
    measure.count_ne_zero ht', (measure.count_apply_lt_top.2 ht).ne,
    measure.count_ne_zero hs', (measure.count_apply_lt_top.2 hs).ne],
end

/-- A version of the law of total probability for counting probabilites. -/
lemma cond_count_add_compl_eq (u t : set Ω) (hs : s.finite) :
  cond_count (s ∩ u) t * cond_count s u + cond_count (s ∩ uᶜ) t * cond_count s uᶜ =
  cond_count s t :=
begin
  conv_rhs { rw [(by simp : s = s ∩ u ∪ s ∩ uᶜ),
    ← cond_count_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
    (disjoint_compl_right.mono inf_le_right inf_le_right)] },
  simp [cond_count_inter_self hs],
end

end probability_theory

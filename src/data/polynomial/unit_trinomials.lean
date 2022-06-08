/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import analysis.complex.polynomial
import data.polynomial.mirror
import ring_theory.roots_of_unity

namespace polynomial
open_locale polynomial

open finset

section semiring

variables {R : Type*} [semiring R] {p q : R[X]}

-- todo: PR to `data/polynomial/basic` with other support lemmas
lemma card_support_eq_one : p.support.card = 1 ↔ ∃ (k : ℕ) (x : R) (hx : x ≠ 0), p = C x * X ^ k :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain hp := card_support_eq_zero.mp (erase_lead_card_support h),
    refine ⟨p.nat_degree, p.leading_coeff, _, _⟩,
    { rw [ne, leading_coeff_eq_zero, ←card_support_eq_zero, h],
      exact one_ne_zero },
    { conv_lhs { rw [←p.erase_lead_add_C_mul_X_pow, hp, zero_add] } } },
  { rintros ⟨k, x, hx, rfl⟩,
    rw [support_C_mul_X_pow k hx, card_singleton] },
end

-- todo: PR to `data/polynomial/basic` with other support lemmas
lemma card_support_eq_two : p.support.card = 2 ↔ ∃ (k m : ℕ) (hkm : k < m)
  (x y : R) (hx : x ≠ 0) (hy : y ≠ 0), p = C x * X ^ k + C y * X ^ m :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨k, x, hx, hp⟩ := card_support_eq_one.mp (erase_lead_card_support h),
    refine ⟨k, p.nat_degree, _, x, p.leading_coeff, hx, _, _⟩,
    { refine lt_of_le_of_lt _ (erase_lead_nat_degree_lt h.ge),
      rw [hp, nat_degree_C_mul_X_pow k x hx] },
    { rw [ne, leading_coeff_eq_zero, ←card_support_eq_zero, h],
      exact two_ne_zero },
    { rw [←hp, erase_lead_add_C_mul_X_pow] } },
  { rintros ⟨k, m, hkm, x, y, hx, hy, rfl⟩,
    exact card_support_binomial hkm.ne hx hy },
end

-- todo: PR to `data/polynomial/basic` with other support lemmas
lemma card_support_eq_three : p.support.card = 3 ↔ ∃ (k m n : ℕ) (hkm : k < m) (hmn : m < n)
  (x y z : R) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0), p = C x * X ^ k + C y * X ^ m + C z * X ^ n :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨k, m, hkm, x, y, hx, hy, hp⟩ := card_support_eq_two.mp (erase_lead_card_support h),
    refine ⟨k, m, p.nat_degree, hkm, _, x, y, p.leading_coeff, hx, hy, _, _⟩,
    { refine lt_of_le_of_lt _ (erase_lead_nat_degree_lt (le_trans (nat.le_succ 2) h.ge)),
      rw [hp, nat_degree_add_eq_right_of_nat_degree_lt, nat_degree_C_mul_X_pow m y hy],
      rwa [nat_degree_C_mul_X_pow k x hx, nat_degree_C_mul_X_pow m y hy] },
    { rw [ne, leading_coeff_eq_zero, ←card_support_eq_zero, h],
      exact three_ne_zero },
    { rw [←hp, erase_lead_add_C_mul_X_pow] } },
  { rintros ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩,
    exact card_support_trinomial hkm hmn hx hy hz },
end

end semiring



/-
OLD STUFF

OLD STUFF

OLD STUFF

OLD STUFF

OLD STUFF

OLD STUFF

OLD STUFF
-/

section semiring

variables {R : Type*} [semiring R] (p : R[X]) {k m n : ℕ} {u v w : R}

lemma trinomial_coeff_k (hkm : k < m) (hmn : m < n) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).coeff k = u :=
by rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
  if_pos rfl, if_neg hkm.ne, if_neg (hkm.trans hmn).ne, add_zero, add_zero]

lemma trinomial_coeff_m (hkm : k < m) (hmn : m < n) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).coeff m = v :=
by rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
  if_neg hkm.ne', if_pos rfl, if_neg hmn.ne, zero_add, add_zero]

lemma trinomial_coeff_n (hkm : k < m) (hmn : m < n) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).coeff n = w :=
by rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
  if_neg (hkm.trans hmn).ne', if_neg hmn.ne', if_pos rfl, zero_add, zero_add]

lemma trinomial_nat_degree (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).nat_degree = n :=
begin
  refine nat_degree_eq_of_degree_eq_some (le_antisymm (sup_le (λ i hi, _))
    (le_degree_of_ne_zero (by rwa trinomial_coeff_n hkm hmn))),
  have := support_trinomial' k m n u v w hi,
  rw [mem_insert, mem_insert, mem_singleton] at this,
  rcases this with rfl | rfl | rfl,
  { exact with_bot.coe_le_coe.mpr (hkm.trans hmn).le },
  { exact with_bot.coe_le_coe.mpr hmn.le },
  { exact le_rfl },
end

lemma trinomial_nat_trailing_degree (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).nat_trailing_degree = k :=
begin
  refine nat_trailing_degree_eq_of_trailing_degree_eq_some (le_antisymm
    (le_trailing_degree_of_ne_zero (by rwa trinomial_coeff_k hkm hmn)) (le_inf (λ i hi, _))),
  have := support_trinomial' k m n u v w hi,
  rw [mem_insert, mem_insert, mem_singleton] at this,
  rcases this with rfl | rfl | rfl,
  { exact le_rfl },
  { exact with_top.coe_le_coe.mpr hkm.le },
  { exact with_top.coe_le_coe.mpr (hkm.trans hmn).le },
end

lemma trinomial_leading_coeff (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).leading_coeff = w :=
by rw [leading_coeff, trinomial_nat_degree hkm hmn hw, trinomial_coeff_n hkm hmn]

lemma trinomial_trailing_coeff (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).trailing_coeff = u :=
by rw [trailing_coeff, trinomial_nat_trailing_degree hkm hmn hu, trinomial_coeff_k hkm hmn]

lemma trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hw : w ≠ 0) :
  (C u * X ^ k + C v * X ^ m + C w * X ^ n).mirror =
    C w * X ^ k + C v * X ^ (n - m + k) + C u * X ^ n :=
by rw [mirror, trinomial_nat_trailing_degree hkm hmn hu, reverse, trinomial_nat_degree hkm hmn hw,
  reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
  rev_at_le (hkm.trans hmn).le, rev_at_le hmn.le, rev_at_le le_rfl, add_mul, add_mul, mul_assoc,
  mul_assoc, mul_assoc, ←pow_add, ←pow_add, ←pow_add, nat.sub_add_cancel (hkm.trans hmn).le,
  nat.sub_self, zero_add, add_comm, add_assoc, add_comm (C u * X ^ n)]

/-- A unit trinomial is a trinomial with unit coefficients. -/
def is_unit_trinomial := ∃ {k m n : ℕ} (hkm : k < m) (hmn : m < n) {u v w : R}
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w), p = C u * X ^ k + C v * X ^ m + C w * X ^ n

variables {p} [nontrivial R]

namespace is_unit_trinomial

lemma card_support_eq_three (hp : p.is_unit_trinomial) : p.support.card = 3 :=
begin
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩ := hp,
  rw [support_trinomial hkm hmn hu.ne_zero hv.ne_zero hw.ne_zero, card_insert_of_not_mem
        (mt mem_insert.mp (not_or hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      card_insert_of_not_mem (mt mem_singleton.mp hmn.ne), card_singleton],
end

lemma ne_zero (hp : p.is_unit_trinomial) : p ≠ 0 :=
begin
  rintro rfl,
  apply nat.zero_ne_bit1 1,
  rw [←hp.card_support_eq_three, support_zero, card_empty],
end

lemma coeff_is_unit (hp : p.is_unit_trinomial) {k : ℕ} (hk : k ∈ p.support) :
  is_unit (p.coeff k) :=
begin
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩ := hp,
  have := support_trinomial' k m n u v w hk,
  rw [mem_insert, mem_insert, mem_singleton] at this,
  rcases this with rfl | rfl | rfl,
  { rwa trinomial_coeff_k hkm hmn },
  { rwa trinomial_coeff_m hkm hmn },
  { rwa trinomial_coeff_n hkm hmn },
end

lemma leading_coeff_is_unit (hp : p.is_unit_trinomial) : is_unit p.leading_coeff :=
hp.coeff_is_unit (nat_degree_mem_support_of_nonzero hp.ne_zero)

lemma trailing_coeff_is_unit (hp : p.is_unit_trinomial) : is_unit p.trailing_coeff :=
hp.coeff_is_unit (nat_trailing_degree_mem_support_of_nonzero hp.ne_zero)

end is_unit_trinomial

lemma is_unit_trinomial_iff :
  p.is_unit_trinomial ↔ p.support.card = 3 ∧ ∀ k ∈ p.support, is_unit (p.coeff k) :=
begin
  refine ⟨λ hp, ⟨hp.card_support_eq_three, λ k, hp.coeff_is_unit⟩, λ hp, _⟩,
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1,
  rw [support_trinomial hkm hmn hx hy hz] at hp,
  replace hx := hp.2 k (mem_insert_self k {m, n}),
  replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n})),
  replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))),
  simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz,
  rw [if_neg hkm.ne, if_neg (hkm.trans hmn).ne] at hx,
  rw [if_neg hkm.ne', if_neg hmn.ne] at hy,
  rw [if_neg (hkm.trans hmn).ne', if_neg hmn.ne'] at hz,
  simp_rw [mul_zero, zero_add, add_zero] at hx hy hz,
  refine ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩,
end

end semiring

section domain

variables {R : Type*} [comm_ring R] [is_domain R] {p : R[X]}

lemma is_unit_trinomial.not_is_unit (hp : p.is_unit_trinomial) : ¬ is_unit p :=
begin
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩ := hp,
  exact λ h, ne_zero_of_lt hmn ((trinomial_nat_degree hkm hmn hw.ne_zero).symm.trans
    (nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit h))),
end

end domain

variables {p q : ℤ[X]}

lemma is_unit_trinomial_iff' : p.is_unit_trinomial ↔ (p * p.mirror).coeff
  (((p * p.mirror).nat_degree + (p * p.mirror).nat_trailing_degree) / 2) = 3 :=
begin
  rw [nat_degree_mul_mirror, nat_trailing_degree_mul_mirror, ←mul_add,
      nat.mul_div_right _ zero_lt_two, coeff_mul_mirror],
  refine ⟨_, λ hp, _⟩,
  { rintros ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩,
    rw [sum_def, support_trinomial hkm hmn hu.ne_zero hv.ne_zero hw.ne_zero,
      sum_insert (mt mem_insert.mp (not_or hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      sum_insert (mt mem_singleton.mp hmn.ne), sum_singleton,
      trinomial_coeff_k hkm hmn, trinomial_coeff_m hkm hmn, trinomial_coeff_n hkm hmn],
    simp only [hu, hv, hw, int.is_unit_sq, bit0, bit1, add_assoc] },
  { have key : ∀ k ∈ p.support, (p.coeff k) ^ 2 = 1 :=
    λ k hk, int.sq_eq_one_of_sq_le_three ((single_le_sum
      (λ k hk, sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk),
    refine is_unit_trinomial_iff.mpr ⟨_,
      λ k hk, is_unit_of_pow_eq_one (p.coeff k) 2 (key k hk) zero_lt_two⟩,
    rw [sum_def, sum_congr rfl key, sum_const, nat.smul_one_eq_coe] at hp,
    exact nat.cast_injective hp },
end

lemma is_unit_trinomial_iff'' (h : p * p.mirror = q * q.mirror) :
  p.is_unit_trinomial ↔ q.is_unit_trinomial :=
by rw [is_unit_trinomial_iff', is_unit_trinomial_iff', h]

namespace is_unit_trinomial

lemma sublemma2 {k m n : ℕ} {u v w : ℤ} (hkm : k < m) (hmn : m < n) (hu : is_unit u)
  (hv : is_unit v) (hw : is_unit w) (hp : p = C u * X ^ k + C v * X ^ m + C w * X ^ n) :
  C v * (C u * X ^ (m + n) + C w * X ^ (n - m + k + n)) =
    ⟨finsupp.filter (set.Ioo (k + n) (n + n)) (p * p.mirror).to_finsupp⟩ :=
begin
  have key : n - m + k < n := by rwa [←lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le],
  rw [hp, trinomial_mirror hkm hmn hu.ne_zero hw.ne_zero],
  simp_rw [←monomial_eq_C_mul_X, add_mul, mul_add, monomial_mul_monomial,
    to_finsupp_add, to_finsupp_monomial, finsupp.filter_add],
  rw [finsupp.filter_single_of_neg, finsupp.filter_single_of_neg, finsupp.filter_single_of_neg,
      finsupp.filter_single_of_neg, finsupp.filter_single_of_neg, finsupp.filter_single_of_pos,
      finsupp.filter_single_of_neg, finsupp.filter_single_of_pos, finsupp.filter_single_of_neg],
  { simp only [add_zero, zero_add, of_finsupp_add, of_finsupp_single],
    rw [C_mul_monomial, C_mul_monomial, mul_comm v w, add_comm (n - m + k) n] },
  { exact λ h, h.2.ne rfl },
  { refine ⟨_, add_lt_add_left key n⟩,
    rwa [add_comm, add_lt_add_iff_left, lt_add_iff_pos_left, tsub_pos_iff_lt] },
  { exact λ h, h.1.ne (add_comm k n) },
  { exact ⟨add_lt_add_right hkm n, add_lt_add_right hmn n⟩ },
  { rw [←add_assoc, add_tsub_cancel_of_le hmn.le, add_comm],
    exact λ h, h.1.ne rfl },
  { intro h,
    have := h.1,
    rw [add_comm, add_lt_add_iff_right] at this,
    exact asymm this hmn },
  { exact λ h, h.1.ne rfl },
  { exact λ h, asymm ((add_lt_add_iff_left k).mp h.1) key },
  { exact λ h, asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn) },
end

lemma binomial_eq_binomial {R : Type*} [semiring R] {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
  C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
  (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) :=
begin
  refine ⟨λ h, _, _⟩,
  { have hk := congr_arg (λ p, coeff p k) h,
    have hl := congr_arg (λ p, coeff p l) h,
    have hm := congr_arg (λ p, coeff p m) h,
    have hn := congr_arg (λ p, coeff p n) h,
    simp only [coeff_add, coeff_C_mul_X_pow, if_pos rfl] at hk hl hm hn,
    by_cases hmk : m = k,
    { by_cases hnl : n = l,
      { exact or.inl ⟨hmk.symm, hnl.symm⟩ },
      { refine (hv _).elim,
        by_cases hlk : l = k,
        { rwa [hmk, ←hlk, if_neg hnl, if_neg hnl, zero_add, zero_add, eq_comm] at hn },
        { rwa [hmk, if_neg hlk, if_neg (ne.symm hnl), zero_add, zero_add] at hl } } },
    { by_cases hkl : k = l,
      { by_cases hmn : m = n,
        { rw [←hkl, if_neg hmk, if_neg hmk, zero_add, eq_comm, if_pos hmn] at hm,
          exact or.inr (or.inr ⟨hm, hkl, hmn⟩) },
        { rw [←hkl, if_neg hmk, if_neg hmk, zero_add, eq_comm, if_neg hmn, add_zero] at hm,
          exact (hu hm).elim } },
      { rw [if_neg (ne.symm hmk), if_neg hkl, zero_add, add_zero] at hk,
        have hkn := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1,
        rw [←hkn, if_neg hmk, if_neg hmk, zero_add, add_zero] at hm,
        have hml := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm hu)).1,
        exact or.inr (or.inl ⟨hk.trans (if_pos hkn), hkn, hml.symm⟩) } } },
  { rintros (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩),
    { refl },
    { apply add_comm },
    { rw [←add_mul, ←add_mul, ←C_add, h, C_0, zero_mul, zero_mul] } },
end

lemma irreducible_step1 {k m m' n : ℕ} {u v w : ℤ}
  (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w)
  (hp : p = C u * X ^ k + C v * X ^ m + C w * X ^ n)
  (hq : q = C u * X ^ k + C v * X ^ m' + C w * X ^ n)
  (h : p * p.mirror = q * q.mirror) :
  q = p ∨ q = p.mirror :=
begin
  let f : polynomial ℤ → polynomial ℤ :=
  λ p, ⟨finsupp.filter (set.Ioo (k + n) (n + n)) p.to_finsupp⟩,
  replace h : f (p * p.mirror) = f (q * q.mirror) := congr_arg f h,
  replace h := (sublemma2 hkm hmn hu hv hw hp).trans h,
  replace h := h.trans (sublemma2 hkm' hmn' hu hv hw hq).symm,
  rw (is_unit_C.mpr hv).mul_right_inj at h,
  rw binomial_eq_binomial hu.ne_zero hw.ne_zero at h,
  simp only [add_left_inj] at h,
  rcases h with ⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩,
  { exact or.inl (hq.trans hp.symm) },
  { refine or.inr _,
    rw [←trinomial_mirror hkm' hmn' hu.ne_zero hw.ne_zero, eq_comm, mirror_eq_iff] at hp,
    exact hq.trans hp },
  { suffices : m = m',
    { rw this at hp,
      exact or.inl (hq.trans hp.symm) },
    rw [tsub_add_eq_add_tsub hmn.le, eq_tsub_iff_add_eq_of_le, ←two_mul] at hm,
    rw [tsub_add_eq_add_tsub hmn'.le, eq_tsub_iff_add_eq_of_le, ←two_mul] at hm',
    exact mul_left_cancel₀ two_ne_zero (hm.trans hm'.symm),
    exact hmn'.le.trans (nat.le_add_right n k),
    exact hmn.le.trans (nat.le_add_right n k) },
end

lemma irreducible_step2 {k m m' n : ℕ} {u v w x z : ℤ}
  (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w) (hx : is_unit x) (hz : is_unit z)
  (hp : p = C u * X ^ k + C v * X ^ m + C w * X ^ n)
  (hq : q = C x * X ^ k + C v * X ^ m' + C z * X ^ n)
  (h : p * p.mirror = q * q.mirror) :
  q = p ∨ q = p.mirror :=
begin
  have hmul := congr_arg leading_coeff h,
  rw [leading_coeff_mul, leading_coeff_mul, mirror_leading_coeff, mirror_leading_coeff, hp, hq,
      trinomial_leading_coeff hkm hmn hw.ne_zero, trinomial_leading_coeff hkm' hmn' hz.ne_zero,
      trinomial_trailing_coeff hkm hmn hu.ne_zero,
      trinomial_trailing_coeff hkm' hmn' hx.ne_zero] at hmul,

  have hadd := congr_arg (eval 1) h,
  rw [eval_mul, eval_mul, mirror_eval_one, mirror_eval_one, ←sq, ←sq, hp, hq] at hadd,
  simp only [eval_add, eval_C_mul, eval_pow, eval_X, one_pow, mul_one] at hadd,
  rw [add_assoc, add_assoc, add_comm u, add_comm x, add_assoc, add_assoc] at hadd,
  simp only [add_sq', add_assoc, add_right_inj, int.is_unit_sq, hu, hv, hw, hx, hz] at hadd,
  rw [mul_assoc, hmul, ←mul_assoc, add_right_inj,
      mul_right_inj' (show 2 * v ≠ 0, from mul_ne_zero two_ne_zero hv.ne_zero)] at hadd,

  rcases (int.is_unit_add_is_unit_eq_is_unit_add_is_unit hw hu hz hx).mp hadd with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { exact irreducible_step1 hkm hmn hkm' hmn' hu hv hw hp hq h },
  { rw [←mirror_inj, trinomial_mirror hkm' hmn' hw.ne_zero hu.ne_zero] at hq,
    rw [mul_comm q, ←q.mirror_mirror, q.mirror.mirror_mirror] at h,
    rw [←mirror_inj, or_comm, ←mirror_eq_iff],
    exact irreducible_step1 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
      ((lt_tsub_iff_right).mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) hu hv hw hp hq h },
end

lemma irreducible_step3 (hp : p.is_unit_trinomial)
  (h : ∀ q : ℤ[X], q ∣ p → q ∣ p.mirror → is_unit q) :
  irreducible p :=
begin
  refine irreducible_of_mirror hp.not_is_unit (λ q hpq, _) h,
  have hq : is_unit_trinomial q := (is_unit_trinomial_iff'' hpq).mp hp,
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, hp⟩ := hp,
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hx, hy, hz, hq⟩ := hq,
  have hk : k = k',
  { rw [←mul_right_inj' (show 2 ≠ 0, from two_ne_zero),
      ←trinomial_nat_trailing_degree hkm hmn hu.ne_zero, ←hp, ←nat_trailing_degree_mul_mirror, hpq,
      nat_trailing_degree_mul_mirror, hq, trinomial_nat_trailing_degree hkm' hmn' hx.ne_zero] },
  have hn : n = n',
  { rw [←mul_right_inj' (show 2 ≠ 0, from two_ne_zero),
      ←trinomial_nat_degree hkm hmn hw.ne_zero, ←hp, ←nat_degree_mul_mirror, hpq,
      nat_degree_mul_mirror, hq, trinomial_nat_degree hkm' hmn' hz.ne_zero] },
  subst hk,
  subst hn,
  rcases eq_or_eq_neg_of_sq_eq_sq y v
    ((int.is_unit_sq hy).trans (int.is_unit_sq hv).symm) with rfl | rfl,
  { rcases irreducible_step2 hkm hmn hkm' hmn' hu hv hw hx hz hp hq hpq with rfl | rfl,
    { exact or.inl rfl },
    { exact or.inr (or.inr (or.inl rfl)) } },
  { rw [←neg_inj, neg_add, neg_add, ←neg_mul, ←neg_mul, ←neg_mul, ←C_neg, ←C_neg, ←C_neg] at hp,
    rw [←neg_mul_neg, ←mirror_neg] at hpq,
    rcases irreducible_step2 hkm hmn hkm' hmn' hu.neg hv.neg hw.neg hx hz hp hq hpq with rfl | rfl,
    { exact or.inr (or.inl rfl) },
    { exact or.inr (or.inr (or.inr p.mirror_neg)) } },
end

lemma irreducible_step4 (hp : is_unit_trinomial p)
  (h : ∀ z : ℂ, ¬ (aeval z p = 0 ∧ aeval z (mirror p) = 0)) : irreducible p :=
begin
  refine hp.irreducible_step3 (λ q hq hq', _),
  suffices : ¬ (0 < q.nat_degree),
  { rw [not_lt, nat.le_zero_iff] at this,
    rw [eq_C_of_nat_degree_eq_zero this, is_unit_C, ←this],
    rcases hq with ⟨p, rfl⟩,
    apply is_unit_of_mul_is_unit_left,
    rw [←leading_coeff, ←leading_coeff_mul],
    exact hp.leading_coeff_is_unit },
  intro hq'',
  have inj : function.injective (algebra_map ℤ ℂ) := (algebra_map ℤ ℂ).injective_int,
  rw [nat_degree_pos_iff_degree_pos, ←degree_map_eq_of_injective inj] at hq'',
  cases complex.exists_root hq'' with z hz,
  apply h z,
  rw [is_root, eval_map, ←aeval_def] at hz,
  split,
  { cases hq with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
  { cases hq' with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
end

lemma irreducible_step5 (hp : is_unit_trinomial p) (h0 : aeval (0 : ℂ) p ≠ 0)
  (h : ∀ (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : z ^ n = 1), aeval z p ≠ 0) : irreducible p :=
begin
  refine hp.irreducible_step4 (λ z hz, _),
  sorry,
end

lemma irreducible_step6 {m n : ℕ} (hm : 0 < m) (hmn : m < n) {u v w : ℤ}
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w)
  (hp : p = C u * X ^ 0 + C v * X ^ m + C w * X ^ n)
  (h : ∀ (n : ℕ) (z : ℂ) (hz : z ^ n = 1), aeval z p ≠ 0) : irreducible p :=
begin
  sorry,
end

lemma irreducible21 (hp : is_unit_trinomial p)
  (μ₃ : ℂ) (μ₆ : ℂ) (hμ₃ : is_primitive_root μ₃ 3)
  (hμ₆ : is_primitive_root μ₆ 6)
  (hp1 : ¬ aeval (0 : ℂ) p = 0)
  (hp2 : ¬ aeval μ₃ p = 0) (hp3 : ¬ aeval μ₆ p = 0) : irreducible p :=
begin
  apply hp.irreducible_step4,
  rintros z ⟨hz1, hz2⟩,
  sorry,
  -- The key is that either p + p.mirror or p - p.mirror will be a unit binomial, so z must be 0
  -- or a root of unity. Then a sum of three roots of unity vanishes, so they must be rotations of
  -- each other.

  -- this lemma is not necessarily true: (X^12 + X^6 + 1) is divisible by 18th cyclotomic polynomial?
  -- but it is true that you only have to check primitive roots of unity,
  -- and you don't have to check 1 or -1
end

-- figure out what the most "user-friendly" statement is (it's probably not the one below)

lemma irreducible3 (hp : is_unit_trinomial p)
  (hp1 : ¬ X ∣ p) (hp2 : ¬ X ^ 2 + X + 1 ∣ p) (hp3 : ¬ X ^ 2 - X + 1 ∣ p) : irreducible p :=
begin
  sorry,
end

end is_unit_trinomial

lemma selmer_irreducible {n : ℕ} (hn : 1 < n) : irreducible (X ^ n - X - 1 : ℤ[X]) :=
begin
  let p : ℤ[X] := X ^ n - X - 1,
  have hp : is_unit_trinomial p,
  { refine ⟨0, 1, n, zero_lt_one, hn, 1, -1, -1, is_unit_one, is_unit_one.neg, is_unit_one.neg, _⟩,
    rw [C_neg, neg_mul, neg_mul, C_1, one_mul, one_mul, one_mul, pow_zero, pow_one],
    sorry },
  refine hp.irreducible3 _ _ _,
  { sorry },
  { sorry },
  { sorry },
end

end polynomial

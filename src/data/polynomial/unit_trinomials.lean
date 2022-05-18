/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import analysis.complex.polynomial
import data.polynomial.mirror

namespace polynomial
open_locale polynomial

open finset

section semiring

variables {R : Type*} [semiring R] {p q : R[X]}

lemma mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
⟨λ h, h ▸ p.mirror_mirror.symm, λ h, h.symm ▸ q.mirror_mirror⟩

lemma mirror_inj : p.mirror = q.mirror ↔ p = q :=
by rw [mirror_eq_iff, mirror_mirror]

lemma support_binomial_le {k m : ℕ} {x y : R} :
  (C x * X ^ k + C y * X ^ m).support ⊆ {k, m} :=
support_add.trans (union_subset ((support_C_mul_X_pow x k).trans
  (singleton_subset_iff.mpr (mem_insert_self k {m}))) ((support_C_mul_X_pow y m).trans
  (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

lemma support_trinomial_le {k m n : ℕ} {x y z : R} :
  (C x * X ^ k + C y * X ^ m + C z * X ^ n).support ⊆ {k, m, n} :=
support_add.trans (union_subset (support_add.trans (union_subset (support_C_mul_X_pow'.trans
  (singleton_subset_iff.mpr (mem_insert_self k {m, n}))) (support_C_mul_X_pow'.trans
  (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
  (support_C_mul_X_pow'.trans (singleton_subset_iff.mpr
  (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

lemma support_binomial_eq {k m : ℕ} (hkm : k < m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (C x * X ^ k + C y * X ^ m).support = {k, m} :=
begin
  refine subset_antisymm support_binomial_le _,
  simp_rw [insert_subset, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne',
    mul_zero, zero_add, add_zero, ne.def, hx, hy, and_self, not_false_iff],
end

lemma support_trinomial_eq {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
  (hy : y ≠ 0) (hz : z ≠ 0) : (C x * X ^ k + C y * X ^ m + C z * X ^ n).support = {k, m, n} :=
begin
  refine subset_antisymm support_trinomial_le _,
  simp_rw [insert_subset, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne', mul_zero, add_zero,
    zero_add, ne.def, hx, hy, hz, and_self, not_false_iff],
end

lemma card_support_binomial_eq {k m : ℕ} (hkm : k < m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (C x * X ^ k + C y * X ^ m).support.card = 2 :=
begin
  rw [support_binomial_eq hkm hx hy, card_insert_of_not_mem, card_singleton],
  rw [mem_singleton],
  exact hkm.ne,
end

lemma card_support_trinomial_eq {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
  (hy : y ≠ 0) (hz : z ≠ 0) : (C x * X ^ k + C y * X ^ m + C z * X ^ n).support.card = 3 :=
begin
  rw [support_trinomial_eq hkm hmn hx hy hz, card_insert_of_not_mem, card_insert_of_not_mem,
      card_singleton],
  { rw [mem_singleton],
    exact hmn.ne },
  { rw [mem_insert, mem_singleton, not_or_distrib],
    exact ⟨hkm.ne, (hkm.trans hmn).ne⟩ },
end

lemma card_support_eq_one : p.support.card = 1 ↔ ∃ (k : ℕ) (x : R) (hx : x ≠ 0), p = C x * X ^ k :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain hp := card_support_eq_zero.mp (erase_lead_card_support h),
    refine ⟨p.nat_degree, p.leading_coeff, _, _⟩,
    { rw [ne, leading_coeff_eq_zero, ←card_support_eq_zero, h],
      exact one_ne_zero },
    { conv_lhs { rw [←p.erase_lead_add_C_mul_X_pow, hp, zero_add] } } },
  { rintros ⟨k, x, hx, rfl⟩,
    rw [support_mul_X_pow x k hx, card_singleton] },
end

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
    exact card_support_binomial_eq hkm hx hy },
end

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
    exact card_support_trinomial_eq hkm hmn hx hy hz },
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
  have := support_trinomial_le hi,
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
  have := support_trinomial_le hi,
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
  rw [support_trinomial_eq hkm hmn hu.ne_zero hv.ne_zero hw.ne_zero, card_insert_of_not_mem
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
  have := support_trinomial_le hk,
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
  rw [support_trinomial_eq hkm hmn hx hy hz] at hp,
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

variables {R : Type*} [comm_ring R] [is_domain R] (p : R[X])

lemma nat_degree_mul_mirror : (p * p.mirror).nat_degree = 2 * p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_degree_zero, mul_zero] },
  rw [nat_degree_mul hp (mt p.mirror_eq_zero.mp hp), mirror_nat_degree, two_mul],
end

lemma nat_trailing_degree_mul_mirror :
  (p * p.mirror).nat_trailing_degree = 2 * p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_trailing_degree_zero, mul_zero] },
  rw [nat_trailing_degree_mul hp (mt p.mirror_eq_zero.mp hp), mirror_nat_trailing_degree, two_mul],
end

variables {p}

lemma is_unit_trinomial.not_is_unit (hp : p.is_unit_trinomial) : ¬ is_unit p :=
begin
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩ := hp,
  exact λ h, ne_zero_of_lt hmn ((trinomial_nat_degree hkm hmn hw.ne_zero).symm.trans
    (nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit h))),
end

end domain

variables {p q : ℤ[X]}

lemma int.sq_eq_one {x : ℤ} (h1 : x ^ 2 < 4) (h2 : x ≠ 0) : x ^ 2 = 1 :=
begin
  let y := |x|,
  replace h1 : |x| < 2,
  { contrapose! h1,
    rw (show (2 : ℤ) = |(2 : ℤ)|, by norm_num) at h1,
    rw show (4 : ℤ) = (2 : ℤ) ^ 2, by norm_num,
    exact sq_le_sq h1 },
  replace h2 : 0 < |x| := abs_pos.mpr h2,
  interval_cases |x|,
  rw [←sq_abs x, h, one_pow],
end

lemma int.sq_eq_one' {x : ℤ} (h1 : x ^ 2 ≤ 3) (h2 : x ≠ 0) : x ^ 2 = 1 :=
int.sq_eq_one (lt_of_le_of_lt h1 (int.lt_succ_self 3)) h2

lemma is_unit_trinomial_iff' : p.is_unit_trinomial ↔ (p * p.mirror).coeff
  (((p * p.mirror).nat_degree + (p * p.mirror).nat_trailing_degree) / 2) = 3 :=
begin
  rw [nat_degree_mul_mirror, nat_trailing_degree_mul_mirror, ←mul_add,
      nat.mul_div_right _ zero_lt_two, coeff_mul_mirror],
  refine ⟨_, λ hp, _⟩,
  { rintros ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩,
    rw [sum_def, support_trinomial_eq hkm hmn hu.ne_zero hv.ne_zero hw.ne_zero,
      sum_insert (mt mem_insert.mp (not_or hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      sum_insert (mt mem_singleton.mp hmn.ne), sum_singleton,
      trinomial_coeff_k hkm hmn, trinomial_coeff_m hkm hmn, trinomial_coeff_n hkm hmn],
    simp only [hu, hv, hw, int.is_unit_sq, bit0, bit1, add_assoc] },
  { have key : ∀ k ∈ p.support, (p.coeff k) ^ 2 = 1 :=
    λ k hk, int.sq_eq_one' ((single_le_sum (λ k hk, sq_nonneg (p.coeff k)) hk).trans hp.le)
        (mem_support_iff.mp hk),
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
  { intro h,
    have := h.1,
    rw [add_lt_add_iff_left] at this,
    exact asymm this key },
  { intro h,
    have := h.1,
    rw [add_lt_add_iff_left] at this,
    exact asymm this (hkm.trans hmn) },
end

lemma sublemma3 {k l m n : ℕ} {u v : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) :
  C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
  (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) :=
begin
  sorry
end

lemma irreducible1_aux3 {k m m' n : ℕ} {u v w : ℤ}
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
  rw sublemma3 hu.ne_zero hw.ne_zero at h,
  simp only [add_left_inj] at h,
  rcases h with h | h | h,
  { rw h.1 at hp,
    exact or.inl (hq.trans hp.symm) },
  { refine or.inr _,
    sorry },
  { refine or.inl _,
    sorry },
end

lemma sublemma {a b c d : ℤ} (ha : is_unit a) (hb : is_unit b) (hc : is_unit c) (hd : is_unit d)
  (h : a + b = c + d) : a = c ∧ b = d ∨ a = d ∧ b = c :=
begin
  by_cases h1 : a = c,
  { rw [h1, add_right_inj] at h,
    exact or.inl ⟨h1, h⟩ },
  by_cases h2 : a = d,
  { rw [h2, add_comm, add_left_inj] at h,
    exact or.inr ⟨h2, h⟩ },
  by_cases h3 : b = d,
  { rw [h3, add_left_inj] at h,
    exact or.inl ⟨h, h3⟩ },
  rcases int.is_unit_eq_one_or hd with rfl | rfl,
  { rw (int.is_unit_eq_one_or ha).resolve_left h2 at h h1,
    rw (int.is_unit_eq_one_or hb).resolve_left h3 at h,
    rw (int.is_unit_eq_one_or hc).resolve_right (ne.symm h1) at h,
    norm_num at h },
  { rw (int.is_unit_eq_one_or ha).resolve_right h2 at h h1,
    rw (int.is_unit_eq_one_or hb).resolve_right h3 at h,
    rw (int.is_unit_eq_one_or hc).resolve_left (ne.symm h1) at h,
    norm_num at h },
end

lemma irreducible1_aux2 {k m m' n : ℕ} {u v w x z : ℤ}
  (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w) (hx : is_unit x) (hz : is_unit z)
  (hp : p = C u * X ^ k + C v * X ^ m + C w * X ^ n)
  (hq : q = C x * X ^ k + C v * X ^ m' + C z * X ^ n)
  (h : p * p.mirror = q * q.mirror) :
  q = p ∨ q = p.mirror :=
begin
  have key2 := congr_arg leading_coeff h,
  simp only [leading_coeff_mul, mirror_leading_coeff] at key2,
  rw [hp, hq, trinomial_leading_coeff hkm hmn hw.ne_zero,
      trinomial_leading_coeff hkm' hmn' hz.ne_zero,
      trinomial_trailing_coeff hkm hmn hu.ne_zero,
      trinomial_trailing_coeff hkm' hmn' hx.ne_zero] at key2,

  have key1 := congr_arg (eval 1) h,
  rw [hp, hq, trinomial_mirror hkm hmn hu.ne_zero hw.ne_zero,
    trinomial_mirror hkm' hmn' hx.ne_zero hz.ne_zero] at key1,
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, one_pow, mul_one, mul_add, add_mul,
    int.is_unit_mul_self, hu, hv, hw, hx, hz] at key1,
  rw [mul_comm u w, mul_comm x z, mul_comm u v, mul_comm w v, mul_comm x v, mul_comm z v, key2] at key1,
  simp_rw [add_assoc, add_right_inj, ←add_assoc, add_left_inj] at key1,
  abel at key1,
  simp_rw [add_right_inj, ←smul_add, smul_eq_mul, ←mul_add] at key1,
  rw [mul_right_inj' (show (2 : ℤ) ≠ (0 : ℤ), from two_ne_zero), mul_right_inj' hv.ne_zero] at key1,

  rcases sublemma hu hw hx hz key1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { exact irreducible1_aux3 hkm hmn hkm' hmn' hu hv hw hp hq h },
  { replace hq := congr_arg mirror hq,
    rw [trinomial_mirror hkm' hmn' hw.ne_zero hu.ne_zero] at hq,
    have key := irreducible1_aux3 hkm hmn _ _ hu hv hw hp hq _,
    { rwa [mirror_inj, mirror_eq_iff, or_comm] at key },
    { rwa [lt_add_iff_pos_left, tsub_pos_iff_lt] },
    { rwa [←lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn'.le] },
    { rwa [mirror_mirror, mul_comm _ q] } },
end

lemma irreducible1 (hp : p.is_unit_trinomial)
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
  rcases eq_or_eq_neg_of_sq_eq_sq y v ((int.is_unit_sq hy).trans (int.is_unit_sq hv).symm) with rfl | rfl,
  { rcases irreducible1_aux2 hkm hmn hkm' hmn' hu hv hw hx hz hp hq hpq with rfl | rfl,
    { exact or.inl rfl },
    { exact or.inr (or.inr (or.inl rfl)) } },
  { rw [←neg_inj, neg_add, neg_add, ←neg_mul, ←neg_mul, ←neg_mul, ←C_neg, ←C_neg, ←C_neg] at hp,
    rcases irreducible1_aux2 hkm hmn hkm' hmn' hu.neg hv.neg hw.neg hx hz hp hq _ with rfl | rfl,
    { exact or.inr (or.inl rfl) },
    { exact or.inr (or.inr (or.inr p.mirror_neg)) },
    { rwa [mirror_neg, neg_mul_neg] } },
end

lemma irreducible2 (hp : is_unit_trinomial p)
  (h : ∀ z : ℂ, ¬ (aeval z p = 0 ∧ aeval z (mirror p) = 0)) : irreducible p :=
begin
  refine hp.irreducible1 (λ q hq hq', _),
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

-- figure out what the most "user-friendly" statement is (it's probably not the one below)

lemma irreducible3 (hp : is_unit_trinomial p)
  (hp1 : ¬ X ∣ p) (hp2 : ¬ X ^ 2 + X + 1 ∣ p) (hp3 : ¬ X ^ 2 - X + 1 ∣ p) : irreducible p :=
begin
  refine hp.irreducible2 (λ z hz, _),
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

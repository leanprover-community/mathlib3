/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import data.real.basic
import algebra.big_operators.ring
import linear_algebra.finite_dimensional
import data.zmod.parity

/-!
# Fisher's inequality

Fisher's inequality for a family of finite sets: Given a finite family `E` of finite sets,
-/

open finset finite_dimensional
open_locale big_operators

@[to_additive] lemma prod_diag {α R : Type*} [decidable_eq α] [comm_monoid R]
  (s : finset α) (f : α → α → R) :
  ∏ i in s.diag, f i.1 i.2 = ∏ i in s, f i i :=
begin
  refine (finset.prod_bij (λ a _, (a, a)) (by simp) _ _ _).symm,
  { simp },
  { simp },
  simp only [mem_diag, exists_prop, and_imp, prod.forall, prod.mk.inj_iff],
  rintro i _ hi rfl,
  exact ⟨i, hi, rfl, rfl⟩,
end

lemma sum_sq {α R : Type*} [decidable_eq α] [comm_ring R] (s : finset α) (f : α → R) :
  (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 + ∑ ij in s.off_diag, f ij.1 * f ij.2 :=
by simp_rw [sq, sum_mul, mul_sum, ←sum_product', ←diag_union_off_diag,
    sum_union (disjoint_diag_off_diag _), sum_diag s (λ i j, f i * f j)]

lemma fisher {ι α : Type*} [fintype ι] [fintype α] [decidable_eq α] (t : ℕ)
  (E : ι → finset α) (hE : ∀ i, t < (E i).card) (hE' : pairwise (λ i j, (E i ∩ E j).card = t)) :
  fintype.card ι ≤ fintype.card α :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  let ind : ι → α → ℝ := λ i a, ite (a ∈ E i) 1 0,
  suffices : linear_independent ℝ ind,
  { simpa using fintype_card_le_finrank_of_linear_independent this },
  rw [fintype.linear_independent_iff],
  intros g hg,
  have h : ∑ i, ((E i).card - t : ℝ) * g i ^ 2 + t * (∑ i, g i) ^ 2 =
    matrix.dot_product (∑ (i : ι), g i • ind i) (∑ (i : ι), g i • ind i),
  { simp_rw [sub_mul, sum_sub_distrib, matrix.dot_product, fintype.sum_apply, pi.smul_apply,
      algebra.id.smul_eq_mul, ←sq, sum_sq, mul_add, mul_sum, ←add_assoc, sub_add_cancel, mul_pow,
      mul_boole, ←ite_and_mul_zero, ite_pow, one_pow, zero_pow' _ two_ne_zero, mul_boole,
      ←mem_inter, sum_add_distrib, @sum_comm _ _ α, ←sum_filter, filter_mem_eq_inter, univ_inter,
      sum_const, nsmul_eq_mul, add_right_inj],
    refine sum_congr rfl (λ i hi, _),
    simp only [mem_off_diag, mem_univ, true_and] at hi,
    rw hE' _ _ hi },
  have : ∀ i ∈ (univ : finset ι), 0 ≤ ((E i).card - t : ℝ) * g i ^ 2 :=
    λ i _, mul_nonneg (by simpa using (hE i).le) (sq_nonneg _),
  rw [hg, matrix.zero_dot_product, add_eq_zero_iff' (sum_nonneg this)
    (mul_nonneg (nat.cast_nonneg _) (sq_nonneg _)), sum_eq_zero_iff_of_nonneg this] at h,
  intro i,
  simpa [(hE i).ne', sub_eq_zero] using h.1 i (mem_univ _),
end

lemma mod_p_town {ι α : Type*} [fintype ι] [fintype α] [decidable_eq α] {p : ℕ} (hp : p.prime)
  (E : ι → finset α) (hE : ∀ i, ¬ p ∣ (E i).card)
  (hE' : pairwise (λ i j, p ∣ (E i ∩ E j).card)) :
  fintype.card ι ≤ fintype.card α :=
begin
  let ind : ι → α → zmod p := λ i a, ite (a ∈ E i) 1 0,
  haveI : fact p.prime := ⟨hp⟩,
  suffices : linear_independent (zmod p) ind,
  { simpa using fintype_card_le_finrank_of_linear_independent this },
  rw [fintype.linear_independent_iff],
  intros g hg j,
  suffices : (↑(E j).card)⁻¹ * matrix.dot_product (∑ i, g i • ind i) (ind j) = g j,
  { rw [←this, hg, matrix.zero_dot_product, mul_zero] },
  simp_rw [matrix.dot_product, fintype.sum_apply, sum_mul, @sum_comm _ _ α, pi.smul_apply,
    algebra.id.smul_eq_mul, mul_assoc, ←ite_and_mul_zero, ←mem_inter, one_mul, mul_boole,
    ←sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul, mul_sum],
  refine (sum_eq_single j (λ i _ h, _) (by simp)).trans _,
  { rw [(zmod.nat_coe_zmod_eq_zero_iff_dvd _ _).2 (hE' _ _ h), zero_mul, mul_zero] },
  rw [inter_self, inv_mul_cancel_left₀ ((zmod.nat_coe_zmod_eq_zero_iff_dvd _ _).not.2 (hE j))],
end

lemma oddtown {ι α : Type*} [fintype ι] [fintype α] [decidable_eq α]
  (E : ι → finset α) (hE : ∀ i, odd (E i).card) (hE' : pairwise (λ i j, even (E i ∩ E j).card)) :
  fintype.card ι ≤ fintype.card α :=
mod_p_town nat.prime_two E
  (λ i, by simpa [nat.odd_iff] using hE i)
  (λ i j h, even_iff_two_dvd.1 (hE' _ _ h))

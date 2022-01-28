/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import number_theory.arithmetic_function
import analysis.special_functions.log

namespace nat
namespace arithmetic_function

/-- In the case when `n` is a prime power, `min_fac` will give the appropriate prime. -/
noncomputable def von_mangoldt : arithmetic_function ℝ :=
⟨λ n, if is_prime_power n then real.log (min_fac n) else 0, if_neg not_is_prime_power_zero⟩

localized "notation `Λ` := nat.arithmetic_function.von_mangoldt" in arithmetic_function

lemma von_mangoldt_apply {n : ℕ} :
  Λ n = if is_prime_power n then real.log (min_fac n) else 0 := rfl

lemma divisors_filter_prime_power' {n : ℕ} :
  n.divisors.filter is_prime_power =
    n.factors.to_finset.bUnion (λ p, ((range (n.factors.count p)).image (λ k, p ^ (k + 1)))) :=
begin
  ext pk,
  simp only [mem_bUnion, mem_image, exists_prop, mem_filter, mem_range, list.mem_to_finset,
    mem_divisors, and_assoc, is_prime_power_iff_pow_succ],
  split,
  { rintro ⟨hdvd, hn, p, k, hp, rfl⟩,
    refine ⟨_, _, _, _, rfl⟩,
    { apply (mem_factors_iff_dvd (nat.pos_of_ne_zero hn) hp).2 (dvd_of_pow_dvd le_add_self hdvd) },
    apply lt_of_lt_of_le _ (list.sublist.count_le (factors_sublist_of_dvd hdvd hn) p),
    rw [hp.factors_pow, list.count_repeat, nat.lt_succ_iff] },
  rintro ⟨p, hp, k, hk, rfl⟩,
  rcases n.eq_zero_or_pos with rfl | hn,
  { simpa using hp },
  refine ⟨_, hn.ne', _, _, prime_of_mem_factors hp, rfl⟩,
  exact (pow_dvd_pow _ hk).trans (pow_factors_count_dvd _ _),
end

lemma divisors_filter_prime_power {n : ℕ} :
  n.divisors.filter is_prime_power =
    n.factors.to_finset.bUnion (λ p, ((Icc 1 (n.factors.count p)).image (λ k, p ^ k))) :=
begin
  rw divisors_filter_prime_power',
  congr,
  ext p,
  rw [←Ico_succ_right, ←image_add_right_Ico 0 _ 1, image_image, range_eq_Ico],
end

lemma multiset.sum_eq {α β : Type*} [decidable_eq α] [add_comm_monoid β]
  (m : finset α) (f : α → multiset β) :
  ∑ i in m, f i = m.val.bind f :=
rfl

lemma prod_powers {n : ℕ} (hn : n ≠ 0) :
  ∏ p in n.factors.to_finset, p ^ n.factors.count p = n :=
begin
  conv_rhs {rw ←prod_factors (nat.pos_of_ne_zero hn)},
  rw [←multiset.coe_prod, ←(n.factors : multiset ℕ).to_finset_sum_count_nsmul_eq, multiset.sum_eq,
    multiset.prod_bind],
  simp only [multiset.coe_count, multiset.nsmul_singleton, multiset.prod_repeat],
  refl
end

lemma thing {n : ℕ} :
  ∑ p in n.factors.to_finset, n.factors.count p • real.log p = real.log n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  conv_rhs { rw ←prod_powers hn.ne' },
  rw [nat.cast_prod, real.log_prod],
  { apply sum_congr rfl,
    intros p hp,
    rw [nat.cast_pow, ←real.rpow_nat_cast, real.log_rpow, _root_.nsmul_eq_mul],
    rw nat.cast_pos,
    apply (prime_of_mem_factors (list.mem_to_finset.1 hp)).pos },
  intros p hp,
  rw nat.cast_ne_zero,
  apply pow_ne_zero,
  exact (prime_of_mem_factors (list.mem_to_finset.1 hp)).pos.ne',
end

lemma von_mangoldt_sum {n : ℕ} :
  ∑ i in n.divisors, Λ i = real.log n :=
begin
  rcases nat.eq_zero_or_pos n with rfl | hn,
  { simp },
  simp only [von_mangoldt_apply],
  rw [←sum_filter, divisors_filter_prime_power', sum_bUnion],
  { have :
      ∑ p in n.factors.to_finset,
        ∑ (i : ℕ) in ((range (n.factors.count p)).image (λ k, p ^ (k + 1))), real.log i.min_fac =
      ∑ p in n.factors.to_finset,
        ∑ (i : ℕ) in ((range (n.factors.count p)).image (λ k, p ^ (k + 1))), real.log p,
    { rw sum_congr rfl (λ p hp, _),
      rw sum_congr rfl (λ pk hpk, _),
      simp only [mem_image, exists_prop, mem_filter, mem_range] at hpk,
      obtain ⟨k, hk, rfl⟩ := hpk,
      rw prime.pow_min_fac (prime_of_mem_factors (list.mem_to_finset.1 hp)) (nat.succ_ne_zero _) },
    rw this,
    simp_rw sum_const,
    have :
      ∑ p in n.factors.to_finset,
        ((range (n.factors.count p)).image (λ k, p ^ (k + 1))).card • real.log p =
      ∑ p in n.factors.to_finset, n.factors.count p • real.log p,
    { rw [sum_congr rfl (λ p hp, _)],
      rw [card_image_of_injective, card_range],
      apply function.injective.comp _ succ_injective,
      apply pow_right_injective (prime_of_mem_factors (list.mem_to_finset.1 hp)).two_le },
    rw [this, thing] },
  simp only [set.pairwise_disjoint, set.pairwise, mem_coe, list.mem_to_finset, ne.def,
    function.on_fun, mem_factors hn, and_imp, disjoint_left, mem_filter, mem_image, and_imp,
    exists_prop, forall_exists_index, mem_range, not_and, not_exists],
  rintro p₁ hp₁ - p₂ hp₂ - hp _ k₁ - h k₂ - rfl,
  exact hp (unique_prime_power hp₁ hp₂ (nat.succ_pos _) h),
end

lemma von_mangoldt_mul_zeta {n : ℕ} :
  (Λ * ζ) n = real.log n :=
by rw [coe_mul_zeta_apply, von_mangoldt_sum]

end arithmetic_function
end nat

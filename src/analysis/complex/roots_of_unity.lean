/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import analysis.special_functions.complex.log
import ring_theory.roots_of_unity

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/

namespace complex

open polynomial real
open_locale nat real

lemma is_primitive_root_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.coprime n) :
  is_primitive_root (exp (2 * π * I * (i / n))) n :=
begin
  rw is_primitive_root.iff_def,
  simp only [← exp_nat_mul, exp_eq_one_iff],
  have hn0 : (n : ℂ) ≠ 0, by exact_mod_cast h0,
  split,
  { use i,
    field_simp [hn0, mul_comm (i : ℂ), mul_comm (n : ℂ)] },
  { simp only [hn0, mul_right_comm _ _ ↑n, mul_left_inj' two_pi_I_ne_zero, ne.def, not_false_iff,
      mul_comm _ (i : ℂ), ← mul_assoc _ (i : ℂ), exists_imp_distrib] with field_simps,
    norm_cast,
    rintro l k hk,
    have : n ∣ i * l,
    { rw [← int.coe_nat_dvd, hk], apply dvd_mul_left },
    exact hi.symm.dvd_of_dvd_mul_left this }
end

lemma is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : is_primitive_root (exp (2 * π * I / n)) n :=
by simpa only [nat.cast_one, one_div]
  using is_primitive_root_exp_of_coprime 1 n h0 n.coprime_one_left

lemma is_primitive_root_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
  is_primitive_root ζ n ↔ (∃ (i < (n : ℕ)) (hi : i.coprime n), exp (2 * π * I * (i / n)) = ζ) :=
begin
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn,
  split, swap,
  { rintro ⟨i, -, hi, rfl⟩, exact is_primitive_root_exp_of_coprime i n hn hi },
  intro h,
  obtain ⟨i, hi, rfl⟩ :=
    (is_primitive_root_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (nat.pos_of_ne_zero hn),
  refine ⟨i, hi, ((is_primitive_root_exp n hn).pow_iff_coprime (nat.pos_of_ne_zero hn) i).mp h, _⟩,
  rw [← exp_nat_mul],
  congr' 1,
  field_simp [hn0, mul_comm (i : ℂ)]
end

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
lemma mem_roots_of_unity (n : ℕ+) (x : units ℂ) :
  x ∈ roots_of_unity n ℂ ↔ (∃ i < (n : ℕ), exp (2 * π * I * (i / n)) = x) :=
begin
  rw [mem_roots_of_unity, units.ext_iff, units.coe_pow, units.coe_one],
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (n.ne_zero),
  split,
  { intro h,
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / n) ^ i = x,
    { simpa only using (is_primitive_root_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos },
    refine ⟨i, hi, _⟩,
    rw [← H, ← exp_nat_mul],
    congr' 1,
    field_simp [hn0, mul_comm (i : ℂ)] },
  { rintro ⟨i, hi, H⟩,
    rw [← H, ← exp_nat_mul, exp_eq_one_iff],
    use i,
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)] }
end

lemma card_roots_of_unity (n : ℕ+) : fintype.card (roots_of_unity n ℂ) = n :=
(is_primitive_root_exp n n.ne_zero).card_roots_of_unity

lemma card_primitive_roots (k : ℕ) : (primitive_roots k ℂ).card = φ k :=
begin
  by_cases h : k = 0,
  { simp [h] },
  exact (is_primitive_root_exp k h).card_primitive_roots,
end

end complex

lemma is_primitive_root.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : is_primitive_root ζ n) (hn : n ≠ 0) :
  ‖ζ‖ = 1 := complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

lemma is_primitive_root.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : is_primitive_root ζ n) (hn : n ≠ 0) :
  ‖ζ‖₊ = 1 := subtype.ext $ h.norm'_eq_one hn

lemma is_primitive_root.arg_ext {n m : ℕ} {ζ μ : ℂ} (hζ : is_primitive_root ζ n)
  (hμ : is_primitive_root μ m) (hn : n ≠ 0) (hm : m ≠ 0) (h : ζ.arg = μ.arg) : ζ = μ :=
complex.ext_abs_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

lemma is_primitive_root.arg_eq_zero_iff {n : ℕ} {ζ : ℂ} (hζ : is_primitive_root ζ n)
  (hn : n ≠ 0) : ζ.arg = 0 ↔ ζ = 1 :=
⟨λ h, hζ.arg_ext is_primitive_root.one hn one_ne_zero (h.trans complex.arg_one.symm),
 λ h, h.symm ▸ complex.arg_one⟩

lemma is_primitive_root.arg_eq_pi_iff {n : ℕ} {ζ : ℂ} (hζ : is_primitive_root ζ n)
  (hn : n ≠ 0) : ζ.arg = real.pi ↔ ζ = -1 :=
⟨λ h, hζ.arg_ext (is_primitive_root.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans complex.arg_neg_one.symm), λ h, h.symm ▸ complex.arg_neg_one⟩

lemma is_primitive_root.arg {n : ℕ} {ζ : ℂ} (h : is_primitive_root ζ n) (hn : n ≠ 0) :
  ∃ i : ℤ, ζ.arg = i / n * (2 * real.pi) ∧ is_coprime i n ∧ i.nat_abs < n :=
begin
  rw complex.is_primitive_root_iff _ _ hn at h,
  obtain ⟨i, h, hin, rfl⟩ := h,
  rw [mul_comm, ←mul_assoc, complex.exp_mul_I],
  refine ⟨if i * 2 ≤ n then i else i - n, _, _, _⟩,
  work_on_goal 2
  { replace hin := nat.is_coprime_iff_coprime.mpr hin,
    split_ifs with _,
    { exact hin },
    { convert hin.add_mul_left_left (-1),
      rw [mul_neg_one, sub_eq_add_neg] } },
  work_on_goal 2
  { split_ifs with h₂,
    { exact_mod_cast h },
    suffices : (i - n : ℤ).nat_abs = n - i,
    { rw this,
      apply tsub_lt_self hn.bot_lt,
      contrapose! h₂,
      rw [nat.eq_zero_of_le_zero h₂, zero_mul],
      exact zero_le _ },
    rw [←int.nat_abs_neg, neg_sub, int.nat_abs_eq_iff],
    exact or.inl (int.coe_nat_sub h.le).symm },
  split_ifs with h₂,
  { convert complex.arg_cos_add_sin_mul_I _,
    { push_cast },
    { push_cast },
    field_simp [hn],
    refine ⟨(neg_lt_neg real.pi_pos).trans_le _, _⟩,
    { rw neg_zero,
      exact mul_nonneg (mul_nonneg i.cast_nonneg $ by simp [real.pi_pos.le]) (by simp) },
    rw [←mul_rotate', mul_div_assoc],
    rw ←mul_one n at h₂,
    exact mul_le_of_le_one_right real.pi_pos.le
      ((div_le_iff' $ by exact_mod_cast (pos_of_gt h)).mpr $ by exact_mod_cast h₂) },
  rw [←complex.cos_sub_two_pi, ←complex.sin_sub_two_pi],
  convert complex.arg_cos_add_sin_mul_I _,
  { push_cast,
    rw [←sub_one_mul, sub_div, div_self],
    exact_mod_cast hn },
  { push_cast,
    rw [←sub_one_mul, sub_div, div_self],
    exact_mod_cast hn },
  field_simp [hn],
  refine ⟨_, le_trans _ real.pi_pos.le⟩,
  work_on_goal 2
  { rw [mul_div_assoc],
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr $ by exact_mod_cast h.le)
      (div_nonneg (by simp [real.pi_pos.le]) $ by simp) },
  rw [←mul_rotate', mul_div_assoc, neg_lt, ←mul_neg, mul_lt_iff_lt_one_right real.pi_pos,
      ←neg_div, ←neg_mul, neg_sub, div_lt_iff, one_mul, sub_mul, sub_lt_comm, ←mul_sub_one],
  norm_num,
  exact_mod_cast not_le.mp h₂,
  { exact (nat.cast_pos.mpr hn.bot_lt) }
end

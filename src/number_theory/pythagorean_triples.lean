/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Paul van Wamelen.
-/
import algebra.field
import algebra.gcd_domain
import algebra.group_with_zero_power
import tactic

/-!
# Pythagorean Triples
The main result is the classification of pythagorean triples. The final result is for general
pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof.
-/

noncomputable theory
open_locale classical

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def pythagorean_triple (x y z : ℤ) : Prop := x*x + y*y = z*z

variables {K : Type*} [field K]

/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circle_equiv_gen (hk : ∀ x : K, 1 + x^2 ≠ 0) :
  K ≃ {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1} :=
{ to_fun := λ x, ⟨⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩,
    by { field_simp [hk x, div_pow], ring },
    by { simp only [ne.def, div_eq_iff (hk x), ←neg_mul_eq_neg_mul, one_mul, neg_add,
      sub_eq_add_neg, add_left_inj],
      rw [eq_neg_iff_add_eq_zero],
      convert hk 1,
      simp }⟩,
  inv_fun := λ p, p.1.1 / (p.1.2 + 1),
  left_inv := λ x,
    begin
      have h2 : (1 + 1 : K) = 2, { norm_num },
      have h3 : (2 : K) ≠ 0, { rw ←h2, convert hk 1, rw one_pow 2 },
      field_simp [hk x, h2, h3, add_assoc, add_comm, add_sub_cancel'_right, mul_comm]
    end,
  right_inv := λ ⟨⟨x, y⟩, hxy, hy⟩,
    begin
      change x ^ 2 + y ^ 2 = 1 at hxy,
      have h2 : y + 1 ≠ 0, { apply mt eq_neg_of_add_eq_zero, exact hy },
      have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1),
      { rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm], ring },
      have h4 : (2 : K) ≠ 0, { rw (by norm_num : (2 : K) = 1 + 1), convert hk 1, rw one_pow 2 },
      simp only [prod.mk.inj_iff, subtype.mk_eq_mk], apply and.intro,
      { field_simp [h2, h3], field_simp [h2, h4, pow_two], ring },
      { field_simp [h2, h3, h4], rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm], ring }
    end }

@[simp] lemma circle_equiv_fun (hk : ∀ x : K, 1 + x^2 ≠ 0) (x : K) :
  (circle_equiv_gen hk x : K × K) = ⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩ := by refl

@[simp] lemma circle_equiv_inv (hk : ∀ x : K, 1 + x^2 ≠ 0)
  (v : {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1}) :
  (circle_equiv_gen hk).symm v = v.val.1 / (v.val.2 + 1) := by refl

private lemma coprime_pow_two_sub_pow_two_sum_of_even_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 0) (hn : n % 2 = 1) :
  int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 :=
begin
  by_contradiction h2,
  cases nat.prime.not_coprime_iff_dvd.mp h2 with p hp,
  have hpp : (p : ℤ) ∣ m ^ 2 + n ^ 2, { exact int.coe_nat_dvd_left.mpr hp.2.2 },
  have hpm : (p : ℤ) ∣ m ^ 2 - n ^ 2, { exact int.coe_nat_dvd_left.mpr hp.2.1 },
  have h2m : (p : ℤ) ∣ 2 * m ^ 2,
  { rw (by ring : 2 * m ^ 2 = m ^ 2 - n ^ 2 + (m ^ 2 + n ^ 2)),
    apply dvd_add hpm hpp },
  have h2n : (p : ℤ) ∣ 2 * n ^ 2,
  { rw (by ring : 2 * n ^ 2 = m ^ 2 + n ^ 2 - (m ^ 2 - n ^ 2)),
    apply dvd_sub hpp hpm },
  have hmc : p = 2 ∨ p ∣ int.nat_abs m, { exact prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp.1 h2m },
  have hnc : p = 2 ∨ p ∣ int.nat_abs n, { exact prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp.1 h2n },
  by_cases hp2 : p = 2,
  { have h3 : (m ^ 2 + n ^ 2) % 2 = 1,
    { rw [int.add_mod, pow_two, pow_two, int.mul_mod, hm, int.mul_mod n n, hn], norm_num },
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0, { apply int.mod_eq_zero_of_dvd, rw hp2 at hpp, exact hpp },
    rw h4 at h3, revert h3, norm_num },
  { have h5 : p ∣ 1, rw ←h, exact nat.dvd_gcd (or.resolve_left hmc hp2) (or.resolve_left hnc hp2),
    apply nat.prime.ne_one hp.1, exact nat.dvd_one.mp h5 }
end

private lemma coprime_pow_two_sub_pow_two_sum_of_odd_even {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 0):
  int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 :=
begin
  dunfold int.gcd,
  rw ←int.nat_abs_neg,
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2), add_comm],
  convert coprime_pow_two_sub_pow_two_sum_of_even_odd _ hn hm, rw [int.gcd_comm], exact h
end

private lemma coprime_pow_two_sub_pow_two_sum_of_odd_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 1) :
    2 ∣ m ^ 2 + n ^ 2
    ∧ 2 ∣ m ^ 2 - n ^ 2
    ∧ ((m ^ 2 - n ^ 2) / 2) % 2 = 0
    ∧ int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
begin
  cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hm) with m0 hm2,
  cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hn) with n0 hn2,
  set a := m0 ^ 2 + n0 ^ 2 + m0 + n0 with ha,
  set b := m0 ^ 2 - n0 ^ 2 + m0 - n0 with hb,
  have h2 : m ^ 2 + n ^ 2 = 2 * (2 * a + 1),
  { rw [ha, pow_two, pow_two, pow_two, pow_two, eq_add_of_sub_eq hm2, eq_add_of_sub_eq hn2], ring },
  have h3 : m ^ 2 - n ^ 2 = 2 * (2 * b),
  { rw [hb, pow_two, pow_two, pow_two, pow_two, eq_add_of_sub_eq hm2, eq_add_of_sub_eq hn2], ring },
  apply and.intro (dvd.intro _ h2.symm),
  apply and.intro (dvd.intro _ h3.symm),
  have h4 : (m ^ 2 + n ^ 2) / 2 = 2 * a + 1,
  { exact int.div_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0) h2},
  have h5 : (m ^ 2 - n ^ 2) / 2 = 2 * b,
  { exact int.div_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0) h3},
  apply and.intro, { rw [h5], norm_num },
  rw [h4, h5],
  by_contradiction h6,
  cases nat.prime.not_coprime_iff_dvd.mp h6 with p hp,
  have hpp : (p : ℤ) ∣ 2 * a + 1, { exact int.coe_nat_dvd_left.mpr hp.2.2 },
  have hpm : (p : ℤ) ∣ 2 * b, { exact int.coe_nat_dvd_left.mpr hp.2.1 },
  have h2m : (p : ℤ) ∣ m ^ 2,
  { have h2m' : m ^ 2 = 2 * a + 1 + 2 * b, {rw [eq_add_of_sub_eq hm2, ha, hb], ring},
    rw h2m', apply dvd_add hpp hpm },
  have h2n : (p : ℤ) ∣ n ^ 2,
  { have h2n' : n ^ 2 = 2 * a + 1 - 2 * b, {rw [eq_add_of_sub_eq hn2, ha, hb], ring},
    rw h2n', apply dvd_sub hpp hpm },
  have hmd : p ∣ int.nat_abs m,
  { apply (or_self _).mp,
    rw [←nat.prime.dvd_mul hp.1, ←int.nat_abs_mul, ←int.coe_nat_dvd_left, ←pow_two],
    exact h2m },
  have hnd : p ∣ int.nat_abs n,
  { apply (or_self _).mp,
    rw [←nat.prime.dvd_mul hp.1, ←int.nat_abs_mul, ←int.coe_nat_dvd_left, ←pow_two],
    exact h2n },
  have h5 : p ∣ 1, { rw ←h, exact nat.dvd_gcd hmd hnd },
  apply nat.prime.ne_one hp.1, exact nat.dvd_one.mp h5
end

lemma ne_zero_of_coprime_pythagorean_triple {x y z : ℤ} (h : pythagorean_triple x y z)
  (hc : int.gcd x y = 1) : z ≠ 0 :=
begin
  change x*x + y*y = z*z at h,
  intro hzz,
  have h2 : 0 < z ^ 2,
  { rw [pow_two, ←h, ←pow_two, ←pow_two],
    have hc' : int.gcd x y ≠ 0, { rw hc, simp },
    cases int.ne_zero_of_gcd hc' with hxz hyz,
    { have h1 : 0 < x ^ 2, { apply lt_of_le_of_ne (pow_two_nonneg x) (pow_ne_zero 2 hxz).symm },
      apply lt_add_of_pos_of_le h1 (pow_two_nonneg y) },
    { have h1 : 0 < y ^ 2, { apply lt_of_le_of_ne (pow_two_nonneg y) (pow_ne_zero 2 hyz).symm },
      apply lt_add_of_le_of_pos (pow_two_nonneg x) h1 } },
  revert h2,
  rw hzz, norm_num
end

lemma exists_coprime_pythagorean_for_zero {x y : ℤ}
  (hc : int.gcd x y = 1) (hx0 : x = 0) :
  ∃ (m n : ℤ), (x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) :=
begin
  change nat.gcd (int.nat_abs x) (int.nat_abs y) = 1 at hc,
  rw [hx0, (by norm_num : int.nat_abs 0 = 0), nat.gcd_zero_left (int.nat_abs y)] at hc,
  cases int.nat_abs_eq y with hy hy,
  { use [(1 : ℤ), (0 : ℤ)], rw [hx0, hy, hc], norm_num },
  { use [(0 : ℤ), (1 : ℤ)], rw [hx0, hy, hc], norm_num }
end

lemma coprime_of_coprime_pythagorean_triple {x y z : ℤ} (h : pythagorean_triple x y z)
  (hc : int.gcd x y = 1) : int.gcd y z = 1 :=
begin
  by_contradiction h2,
  cases nat.prime.not_coprime_iff_dvd.mp h2 with p hp,
  have h3 : p ∣ int.nat_abs x,
  { apply (or_self _).mp,
    rw [←nat.prime.dvd_mul hp.1, ←int.nat_abs_mul, ←int.coe_nat_dvd_left],
    rw (eq_sub_of_add_eq h),
    apply dvd_sub,
    { apply dvd_mul_of_dvd_left (int.coe_nat_dvd_left.mpr hp.2.2) },
    { apply dvd_mul_of_dvd_left (int.coe_nat_dvd_left.mpr hp.2.1) } },
  have h4 : p ∣ 1, { rw ←hc, apply nat.dvd_gcd h3 hp.2.1 },
  apply nat.prime.ne_one hp.1, exact nat.dvd_one.mp h4
end

theorem exists_coprime_pythagorean_triple_of_odd {x y z : ℤ} (h : pythagorean_triple x y z)
  (hc : int.gcd x y = 1) (hyo : y % 2 = 1) (hzpos : 0 < z):
  ∃ (m n : ℤ), (x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) :=
begin
  set v := (x : ℚ) / z with hv,
  set w := (y : ℚ) / z with hw,
  have hz : z ≠ 0, apply ne_of_gt hzpos,
  have hq : v ^ 2 + w ^ 2 = 1,
  { rw [hv, hw], field_simp [hz], norm_cast,
    rw [pow_two, pow_two, pow_two], exact h },
  by_cases h0 : x = 0, { exact exists_coprime_pythagorean_for_zero hc h0 },
  have hvz : v ≠ 0, { rw hv, field_simp [hz], exact h0 },
  have hw1 : w ≠ -1,
  { intro h2, apply hvz, apply @pow_eq_zero _ _ _ 2, rw [eq_sub_of_add_eq hq, h2], norm_num },
  have hQ : ∀ x : ℚ, 1 + x^2 ≠ 0,
  { intro q, apply ne_of_gt,
    apply lt_add_of_pos_of_le, norm_num, exact pow_two_nonneg q },
  have hp : (⟨v, w⟩ : ℚ × ℚ) ∈ {p : ℚ × ℚ | p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1},
  { rw set.mem_set_of_eq, apply and.intro, exact hq, exact hw1},
  set q := (circle_equiv_gen hQ).inv_fun ⟨⟨v, w⟩, hp⟩ with hq,
  have ht0 : (⟨⟨v, w⟩, hp⟩ : {p : ℚ × ℚ | p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1}) = (circle_equiv_gen hQ).to_fun q,
  { rw hq, apply ((circle_equiv_gen hQ).right_inv _).symm },
  have ht3 : (⟨v, w⟩ : ℚ × ℚ) = ⟨2 * q / (1 + q ^ 2), (1 - q ^ 2) / (1 + q ^ 2)⟩,
  { apply congr_arg subtype.val ht0 },
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2), { exact prod.mk.inj ht3 },
  set m := (q.denom : ℤ) with hm,
  set n := q.num with hn;
  have hm0 : m ≠ 0, { rw hm, norm_num, apply rat.denom_ne_zero q },
  have hm2n20 : m ^ 2 + n ^ 2 > 0,
  { apply lt_add_of_pos_of_le _ (pow_two_nonneg n),
    exact lt_of_le_of_ne (pow_two_nonneg m) (ne.symm (pow_ne_zero 2 hm0)) },
  have hq2 : q = n / m, { rw [hm, hn, int.cast_coe_nat], exact (rat.cast_id q).symm },
  have hw2 : w = (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2),
  { rw [ht4.2, hq2], field_simp [hm2n20, (rat.denom_ne_zero q)] },
  have hm2n20' : (m : ℚ) ^ 2 + (n : ℚ) ^ 2 ≠ 0, { norm_cast, convert ne_of_gt hm2n20, ring },
  have hv2 : v = 2 * m * n / (m ^ 2 + n ^ 2),
  { apply eq.symm, apply (div_eq_iff hm2n20').mpr, rw [ht4.1], field_simp [hQ q],
    rw [hq2] {occs := occurrences.pos [2, 3]}, field_simp [rat.denom_ne_zero q], ring },
  have hmncp : int.gcd n m = 1, { rw [hm, hn], exact q.cop },
  have hnmcp : int.gcd m n = 1, { rw int.gcd_comm, exact hmncp },
  cases int.mod_two_eq_zero_or_one m with hm2 hm2,
  { cases int.mod_two_eq_zero_or_one n with hn2 hn2,
    { -- m even, n even
      exfalso,
      have h1 : 2 ∣ (int.gcd n m : ℤ),
      { exact int.dvd_gcd (int.dvd_of_mod_eq_zero hn2) (int.dvd_of_mod_eq_zero hm2) },
      rw hmncp at h1, revert h1, norm_num },
    { -- m even, n odd
      have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2,
      { apply rat.div_int_inj hzpos hm2n20 (coprime_of_coprime_pythagorean_triple h hc)
          (coprime_pow_two_sub_pow_two_sum_of_even_odd hnmcp hm2 hn2),
        { rw [←hw, hw2], norm_cast } },
      use [m, n],
      apply and.intro,
      { apply (rat.coe_int_inj _ _).mp,
        apply (div_left_inj' ((mt (rat.coe_int_inj z 0).mp) hz)).mp,
        rw [←hv, h2.right, hv2], norm_cast },
      exact h2.left } },
  { cases int.mod_two_eq_zero_or_one n with hn2 hn2,
    { -- m odd, n even
      have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2,
      { apply rat.div_int_inj hzpos hm2n20 (coprime_of_coprime_pythagorean_triple h hc)
          (coprime_pow_two_sub_pow_two_sum_of_odd_even hnmcp hm2 hn2),
        { rw [←hw, hw2], norm_cast } },
      use [m, n],
      apply and.intro,
      { apply (rat.coe_int_inj _ _).mp,
        apply (div_left_inj' ((mt (@rat.coe_int_inj z 0).mp) hz)).mp,
        rw [←hv, h2.right, hv2], norm_cast },
      exact h2.left },
    { -- m odd, n odd
      exfalso,
      have h1 : 2 ∣ m ^ 2 + n ^ 2 ∧ 2 ∣ m ^ 2 - n ^ 2
        ∧ ((m ^ 2 - n ^ 2) / 2) % 2 = 0 ∧ int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1,
      { exact coprime_pow_two_sub_pow_two_sum_of_odd_odd hnmcp hm2 hn2 },
      have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2,
      { apply rat.div_int_inj hzpos _ (coprime_of_coprime_pythagorean_triple h hc) h1.2.2.2,
        { rw [←hw, ←rat.mk_eq_div, ←(rat.div_mk_div_cancel_left (by norm_num : (2 : ℤ) ≠ 0))],
          rw [int.div_mul_cancel h1.1, int.div_mul_cancel h1.2.1, hw2], norm_cast },
        { apply (mul_lt_mul_right (by norm_num : 0 < (2 : ℤ))).mp,
          rw [int.div_mul_cancel h1.1, zero_mul], exact hm2n20 } },
      rw [h2.1, h1.2.2.1] at hyo,
      revert hyo,
      norm_num } }
end

theorem pythagorean_triple_symm {x y z : ℤ} (h : pythagorean_triple x y z)
  : pythagorean_triple y x z :=
begin
  dunfold pythagorean_triple, rw add_comm, exact h
end

lemma odd_even_of_coprime_pythagorean_triple {x y z : ℤ} (h : pythagorean_triple x y z)
  (hc : int.gcd x y = 1) : (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) :=
begin
  cases int.mod_two_eq_zero_or_one x with hx hx,
  { cases int.mod_two_eq_zero_or_one y with hy hy,
    { -- x even, y even
      exfalso,
      apply nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) _ _ hc,
      { apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hx },
      { apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hy }},
    { tauto }}, -- x even, y odd
  { cases int.mod_two_eq_zero_or_one y with hy hy,
    { tauto }, -- x odd, y even
    { -- x odd, y odd
      exfalso,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      change x * x + y * y = z * z at h,
      have h4 : z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2,
      { rw [←h, eq_add_of_sub_eq hx2, eq_add_of_sub_eq hy2], ring },
      have h5 : z * z % 4 = 2,
      { rw h4, simp [int.add_mod, int.mul_mod_right], norm_num },
      revert h5,
      cases int.mod_two_eq_zero_or_one z with hz hz,
      { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hz) with z0 hz2,
        rw [eq_add_of_sub_eq hz2],
        rw (by ring : (z0 * 2 + 0) * (z0 * 2 + 0) = 4 * z0 * z0),
        rw [mul_assoc, int.mul_mod_right],
        norm_num },
      { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hz) with z0 hz2,
        rw [eq_add_of_sub_eq hz2],
        rw (by ring : (z0 * 2 + 1) * (z0 * 2 + 1) = 4 * (z0 * z0 + z0) + 1),
        rw [int.add_mod, int.mul_mod_right],
        norm_num } } }
end

theorem exists_coprime_pythagorean_triple_pos {x y z : ℤ}
  (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) (hzpos : 0 < z):
  (∃ (m n : ℤ), (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n))
  ∨ ∃ (m n : ℤ), (x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) :=
begin
  cases odd_even_of_coprime_pythagorean_triple h hc with h1 h2,
  { apply or.intro_right, exact (exists_coprime_pythagorean_triple_of_odd h hc h1.right hzpos) },
  apply or.intro_left, rw int.gcd_comm at hc,
  have h2 : ∃ (m n : ℤ), y = 2 * m * n ∧ x = m ^ 2 - n ^ 2,
  { exact (exists_coprime_pythagorean_triple_of_odd (pythagorean_triple_symm h) hc h2.left hzpos) },
  tauto
end

theorem exists_coprime_pythagorean_triple {x y z : ℤ}
  (h : pythagorean_triple x y z) (hc : int.gcd x y = 1) :
  (∃ (m n : ℤ), (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n))
  ∨ ∃ (m n : ℤ), (x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) :=
begin
  by_cases hz : 0 < z,
  { exact exists_coprime_pythagorean_triple_pos h hc hz },
  have h' : pythagorean_triple x y (-z),
  { unfold pythagorean_triple, rw neg_mul_neg, exact h },
  apply exists_coprime_pythagorean_triple_pos h' hc,
  apply lt_of_le_of_ne _ (ne.symm (ne_zero_of_coprime_pythagorean_triple h' hc)),
  exact le_neg.mp (not_lt.mp hz)
end

theorem exists_pythagorean_triple {x y z : ℤ}
  (h : pythagorean_triple x y z) :
  (∃ (k m n : ℤ), (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n)))
  ∨ ∃ (k m n : ℤ), (x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx0 : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy0 : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    apply or.intro_right, use [(0 : ℤ), (0 : ℤ), (0 : ℤ)], rw [hx0, hy0],
    norm_num },
  rcases int.exists_gcd_one' (nat.pos_of_ne_zero h0) with ⟨k, x0, y0, k0, h2, hx0, hy0⟩,
  dunfold pythagorean_triple at h,
  have hz : (k : ℤ) ^ 2 ∣ z ^ 2,
  { rw [pow_two z, ← h, hx0, hy0],
    rw (by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = k ^ 2 * (x0 * x0 + y0 * y0)),
    apply dvd_mul_right },
  have hz0 : ∃ z0, z = z0 * k,
  { exact exists_eq_mul_left_of_dvd ((int.pow_dvd_pow_iff (by norm_num : 0 < 2)).mp hz) },
  cases hz0 with z0 hz0,
  have h' : pythagorean_triple x0 y0 z0,
  { dunfold pythagorean_triple,
    have hk0 : (k : ℤ) ^ 2 ≠ 0, { apply pow_ne_zero 2, exact int.coe_nat_ne_zero_iff_pos.mpr k0 },
    apply (domain.mul_left_inj hk0).mp,
    rw [hz0, hx0, hy0] at h,
    rw [(by ring : z0 * z0 * (k : ℤ) ^ 2 = z0 * k * (z0 * k)), ←h],
    ring },
  rcases exists_coprime_pythagorean_triple h' h2 with ⟨m, ⟨n, hmn⟩⟩ | ⟨m, ⟨n, hmn⟩⟩,
  { apply or.intro_left, use [k, m, n],
    rw [hx0, hy0, hmn.left, hmn.right], apply and.intro; ring },
  { apply or.intro_right, use [k, m, n],
    rw [hx0, hy0, hmn.left, hmn.right], apply and.intro; ring }
end

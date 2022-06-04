/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import number_theory.padics.padic_val
import analysis.special_functions.log.basic

import algebraic_geometry.EllipticCurve.torsion

/-!
# The Mordell-Weil theorem for an elliptic curve over the rationals
-/

noncomputable theory
open_locale big_operators classical

----------------------------------------------------------------------------------------------------
/-! ## Lemmas -/

lemma zero_le_three {α : Type} [ordered_semiring α] : (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

namespace padic_val_nat

variables (n : ℕ)

/-- A factor is a prime of non-zero valuation. -/
def ne_zero_of_factorization :
  n.factorization.support → {p : ℕ // p.prime ∧ padic_val_nat p n ≠ 0} :=
λ ⟨p, hp⟩, ⟨p, let hp' := nat.prime_of_mem_factorization hp in
  ⟨hp', (@padic_val_nat_eq_factorization p n ⟨hp'⟩).symm ▸ finsupp.mem_support_iff.mp hp⟩⟩

lemma ne_zero_of_factorization.bijective : function.bijective $ ne_zero_of_factorization n :=
⟨λ ⟨_, _⟩ ⟨_, _⟩ hp, subtype.mk_eq_mk.mpr $ subtype.mk.inj_arrow hp id, λ ⟨p, ⟨hp, hpn⟩⟩,
  ⟨⟨p, finsupp.mem_support_iff.mpr ((@padic_val_nat_eq_factorization p n ⟨hp⟩) ▸ hpn)⟩, rfl⟩⟩

instance ne_zero.fintype : fintype {p : ℕ // p.prime ∧ padic_val_nat p n ≠ 0} :=
fintype.of_bijective (ne_zero_of_factorization n) (ne_zero_of_factorization.bijective n)

@[simp] lemma finprod_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
  ∏ p : {p : ℕ // p.prime ∧ padic_val_nat p n ≠ 0}, (p : ℕ) ^ padic_val_nat p n = n :=
begin
  symmetry,
  nth_rewrite_lhs 0 [← nat.factorization_prod_pow_eq_self hn],
  rw [finsupp.prod, ← finset.prod_coe_sort],
  apply fintype.prod_bijective (ne_zero_of_factorization n) (ne_zero_of_factorization.bijective n),
  rintro ⟨p, hp⟩,
  rw [subtype.coe_mk, ← @padic_val_nat_eq_factorization p n ⟨nat.prime_of_mem_factorization hp⟩],
  refl
end

end padic_val_nat

namespace padic_val_int

variables (z : ℤ)

instance ne_zero.fintype : fintype {p : ℕ // p.prime ∧ padic_val_int p z ≠ 0} :=
by { simp_rw [padic_val_int], exact padic_val_nat.ne_zero.fintype z.nat_abs }

@[simp] lemma finprod_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
  ∏ p : {p : ℕ // p.prime ∧ padic_val_int p n ≠ 0}, (p : ℕ) ^ padic_val_int p n = n.nat_abs :=
padic_val_nat.finprod_of_ne_zero $ int.nat_abs_ne_zero_of_ne_zero hn

end padic_val_int

namespace padic_val_rat

variables (p : ℕ) [fact p.prime] (q : ℚ)

lemma add_of_lt {q r : ℚ} (hq : q ≠ 0) (hlt : padic_val_rat p q < padic_val_rat p r) :
  padic_val_rat p (q + r) = padic_val_rat p q :=
begin
  rw [le_antisymm_iff],
  split,
  { rw [← add_sub_cancel q r] at hq,
    rw [← add_sub_cancel q r, ← padic_val_rat.neg r] at hlt,
    nth_rewrite_rhs 0 [← add_sub_cancel q r],
    exact or.resolve_right (min_le_iff.mp $ min_le_padic_val_rat_add p hq) (not_le_of_lt hlt) },
  { by_cases hqr : q + r = 0,
    { rw [add_eq_zero_iff_eq_neg] at hqr,
      rw [hqr, padic_val_rat.neg] at hlt,
      exact false.elim (has_lt.lt.false hlt) },
    exact le_padic_val_rat_add_of_le p hqr (le_of_lt hlt) },
end

lemma num_or_denom_eq_zero : padic_val_int p q.num = 0 ∨ padic_val_nat p q.denom = 0 :=
begin
  simp only [padic_val_int, padic_val_nat, multiplicity, enat.find_get],
  split_ifs,
  any_goals { simp only [nat.find_eq_zero, pow_one, eq_self_iff_true, or_true, true_or] },
  by_cases hdenom : p ∣ q.denom,
  { exact or.inl
      (λ hnum, nat.not_coprime_of_dvd_of_dvd (nat.prime.one_lt _inst_1.elim) hnum hdenom q.cop) },
  { exact or.inr hdenom }
end

lemma eq_zero_iff :
  padic_val_rat p q = 0 ↔ padic_val_int p q.num = 0 ∧ padic_val_nat p q.denom = 0 :=
begin
  rw [padic_val_rat, sub_eq_zero, int.coe_nat_inj'],
  split,
  { intro hq,
    cases num_or_denom_eq_zero p q,
    { exact ⟨h, hq ▸ h⟩ },
    { exact ⟨hq.symm ▸ h, h⟩ } },
  { rintro ⟨hnum, hdenom⟩,
    rw [hnum, hdenom] }
end

lemma eq_num.tfae : tfae [padic_val_rat p q = padic_val_int p q.num,
  padic_val_nat p q.denom = 0, 0 ≤ padic_val_rat p q] :=
begin
  rw [padic_val_rat, sub_eq_self, int.coe_nat_eq_zero, sub_nonneg, int.coe_nat_le],
  tfae_have : 1 ↔ 2,
  { refl },
  tfae_have : 2 → 3,
  { intro hdenom,
    simpa only [hdenom] using nat.zero_le (padic_val_int p q.num) },
  tfae_have : 3 → 2,
  { intro hq,
    cases num_or_denom_eq_zero p q with hnum hdenom,
    { rwa [hnum, nat.le_zero_iff] at hq },
    { exact hdenom } },
  tfae_finish
end

lemma neg_iff : padic_val_rat p q < 0 ↔ padic_val_nat p q.denom ≠ 0 :=
iff.trans not_le.symm $ not_iff_not_of_iff $ (eq_num.tfae p q).out 2 1

lemma neg_iff' (p : ℕ) (q : ℚ) :
  p.prime ∧ padic_val_rat p q < 0 ↔ p.prime ∧ padic_val_nat p q.denom ≠ 0 :=
⟨λ ⟨hp, hpq⟩, ⟨hp, (@neg_iff p ⟨hp⟩ q).mp hpq⟩, λ ⟨hp, hpq⟩, ⟨hp, (@neg_iff p ⟨hp⟩ q).mpr hpq⟩⟩

/-- A prime of non-zero denominator valuation has negative valuation. -/
def neg_of_denom_ne_zero :
  {p : ℕ // p.prime ∧ padic_val_nat p q.denom ≠ 0} → {p : ℕ // p.prime ∧ padic_val_rat p q < 0} :=
λ ⟨p, hp⟩, ⟨p, (neg_iff' p q).mpr hp⟩

lemma neg_of_denom_ne_zero.bijective : function.bijective $ neg_of_denom_ne_zero q :=
⟨λ ⟨_, _⟩ ⟨_, _⟩ h, subtype.mk_eq_mk.mpr $ subtype.mk.inj_arrow h id,
  λ ⟨p, hp⟩, ⟨⟨p, (@neg_iff' p q).mp hp⟩, rfl⟩⟩

instance neg.fintype : fintype {p : ℕ // p.prime ∧ padic_val_rat p q < 0} :=
fintype.of_bijective (neg_of_denom_ne_zero q) (neg_of_denom_ne_zero.bijective q)

@[simp] lemma finprod_of_neg {q : ℚ} :
  ∏ p : {p : ℕ // p.prime ∧ padic_val_rat p q < 0}, (p : ℕ) ^ padic_val_nat p q.denom = q.denom :=
begin
  nth_rewrite_rhs 0 [← padic_val_nat.finprod_of_ne_zero $ ne_zero_of_lt q.pos],
  rw [fintype.prod_bijective (neg_of_denom_ne_zero q) (neg_of_denom_ne_zero.bijective q)],
  exact λ ⟨_, _⟩, rfl
end

lemma eq_denom.tfae : tfae [padic_val_rat p q = -padic_val_nat p q.denom,
  padic_val_int p q.num = 0, padic_val_rat p q ≤ 0] :=
begin
  rw [padic_val_rat, sub_eq_neg_self, int.coe_nat_eq_zero, sub_nonpos, int.coe_nat_le],
  tfae_have : 1 ↔ 2,
  { refl },
  tfae_have : 2 → 3,
  { intro hnum,
    simpa only [hnum] using nat.zero_le (padic_val_nat p q.denom) },
  tfae_have : 3 → 2,
  { intro hq,
    cases num_or_denom_eq_zero p q with hnum hdenom,
    { exact hnum },
    { rwa [hdenom, nat.le_zero_iff] at hq } },
  tfae_finish
end

lemma pos_iff : 0 < padic_val_rat p q ↔ padic_val_int p q.num ≠ 0 :=
iff.trans not_le.symm $ not_iff_not_of_iff $ (eq_denom.tfae p q).out 2 1

lemma pos_iff' (p : ℕ) (q : ℚ) :
  p.prime ∧ 0 < padic_val_rat p q ↔ p.prime ∧ padic_val_int p q.num ≠ 0 :=
⟨λ ⟨hp, hpq⟩, ⟨hp, (@pos_iff p ⟨hp⟩ q).mp hpq⟩, λ ⟨hp, hpq⟩, ⟨hp, (@pos_iff p ⟨hp⟩ q).mpr hpq⟩⟩

/-- A prime of non-zero numerator valuation has positive valuation. -/
def pos_of_num_ne_zero :
  {p : ℕ // p.prime ∧ padic_val_int p q.num ≠ 0} → {p : ℕ // p.prime ∧ 0 < padic_val_rat p q} :=
λ ⟨p, hp⟩, ⟨p, (pos_iff' p q).mpr hp⟩

lemma pos_of_num_ne_zero.bijective : function.bijective $ pos_of_num_ne_zero q :=
⟨λ ⟨_, _⟩ ⟨_, _⟩ h, subtype.mk_eq_mk.mpr $ subtype.mk.inj_arrow h id,
  λ ⟨p, hp⟩, ⟨⟨p, (@pos_iff' p q).mp hp⟩, rfl⟩⟩

instance pos.fintype : fintype {p : ℕ // p.prime ∧ 0 < padic_val_rat p q} :=
fintype.of_bijective (pos_of_num_ne_zero q) (pos_of_num_ne_zero.bijective q)

@[simp] lemma finprod_of_pos {q : ℚ} (hq : q ≠ 0) :
  ∏ p : {p : ℕ // p.prime ∧ 0 < padic_val_rat p q}, (p : ℕ) ^ padic_val_int p q.num
    = q.num.nat_abs :=
begin
  rw [← padic_val_int.finprod_of_ne_zero $ rat.num_ne_zero_of_ne_zero hq,
      fintype.prod_bijective (pos_of_num_ne_zero q) (pos_of_num_ne_zero.bijective q)],
  exact λ ⟨_, _⟩, rfl
end

end padic_val_rat

----------------------------------------------------------------------------------------------------
/-! ## p-adic valuations of points -/

namespace padic_val_point

variables {A B : ℤ} {x y : ℚ} (w : y ^ 2 = x ^ 3 + A * x + B) {p : ℕ} [fact p.prime]

include w

lemma y_of_x_nonneg (hpx : 0 ≤ padic_val_rat p x) : 0 ≤ padic_val_rat p y :=
begin
  by_cases hx3AxB : x ^ 3 + A * x + B = 0,
  { rw [hx3AxB, sq_eq_zero_iff] at w,
    rw [w, padic_val_rat.zero] },
  have hy : y ≠ 0 := by { rintro rfl, rw [zero_pow zero_lt_two] at w, exact hx3AxB w.symm },
  apply_fun padic_val_rat p at w,
  by_cases hx3Ax : x ^ 3 + A * x = 0,
  { rw [padic_val_rat.pow p hy, hx3Ax, zero_add, padic_val_rat.of_int] at w,
    exact (mul_nonneg_iff_right_nonneg_of_pos zero_lt_two).mp (w.symm ▸ int.coe_nat_nonneg _) },
  have hx : x ≠ 0 :=
  begin
    rintro rfl,
    rw [zero_pow zero_lt_three, zero_add, mul_zero] at hx3Ax,
    exact false_of_ne hx3Ax
  end,
  have hpx3 : 0 ≤ padic_val_rat p (x ^ 3) :=
  by simpa only [padic_val_rat.pow p hx]
     using (mul_nonneg_iff_right_nonneg_of_pos zero_lt_three).mpr hpx,
  have hpAx : 0 ≤ padic_val_rat p (A * x) :=
  begin
    by_cases hA : (A : ℚ) = 0,
    { rw [hA, zero_mul, padic_val_rat.zero] },
    { simpa only [padic_val_rat.mul p hA hx, padic_val_rat.of_int]
      using add_nonneg (int.coe_nat_nonneg _) hpx }
  end,
  have hpB : 0 ≤ padic_val_rat p B :=
  begin
    by_cases hB : (B : ℚ) = 0,
    { rw [hB, padic_val_rat.zero] },
    { simpa only [padic_val_rat.of_int] using int.coe_nat_nonneg _ }
  end,
  have hpy2 : 0 ≤ padic_val_rat p (x ^ 3 + A * x + B) :=
  le_trans
    (le_min (le_trans (le_min hpx3 hpAx) $ padic_val_rat.min_le_padic_val_rat_add p hx3Ax) hpB)
    (padic_val_rat.min_le_padic_val_rat_add p hx3AxB),
  rw [← w, padic_val_rat.pow p hy] at hpy2,
  exact nonneg_of_mul_nonneg_left hpy2 zero_lt_two
end

lemma of_x_neg (hpx : padic_val_rat p x < 0) :
  ∃ n : ℕ, padic_val_rat p x = -(2 * n) ∧ padic_val_rat p y = -(3 * n) :=
begin
  have hx : x ≠ 0 := by { intro hx, rw [hx, padic_val_rat.zero] at hpx, exact has_lt.lt.false hpx },
  have hx3Ax : x ^ 3 + A * x ≠ 0 :=
  begin
    intro hx3Ax,
    rw [add_eq_zero_iff_eq_neg] at hx3Ax,
    have hA : (A : ℚ) ≠ 0 := λ hA, by { rw [hA, zero_mul] at hx3Ax, exact hx (pow_eq_zero hx3Ax) },
    have hpA : 0 ≤ (padic_val_int p A : ℤ) := int.coe_nat_nonneg _,
    apply_fun padic_val_rat p at hx3Ax,
    rw [padic_val_rat.pow p hx, int.coe_nat_succ, add_mul, one_mul, padic_val_rat.neg,
        padic_val_rat.mul p hA hx, add_right_cancel_iff, padic_val_rat.of_int] at hx3Ax,
    rw [← hx3Ax] at hpA,
    exact not_lt_of_le (nonneg_of_mul_nonneg_left hpA zero_lt_two) hpx
  end,
  have hpx3Ax : padic_val_rat p (x ^ 3 + A * x) = padic_val_rat p (x ^ 3) :=
  begin
    apply padic_val_rat.add_of_lt p (pow_ne_zero 3 hx),
    rw [padic_val_rat.pow p hx],
    by_cases hA : (A : ℚ) = 0,
    { simpa only [hA, zero_mul, padic_val_rat.zero] using mul_neg_of_pos_of_neg zero_lt_three hpx },
    rw [int.coe_nat_succ, add_mul, one_mul, padic_val_rat.mul p hA hx, add_lt_add_iff_right,
        padic_val_rat.of_int],
    exact lt_of_lt_of_le (mul_neg_of_pos_of_neg zero_lt_two hpx) (int.coe_nat_nonneg _)
  end,
  have hx3AxB : x ^ 3 + A * x + B ≠ 0 :=
  begin
    intro hx3AxB,
    rw [add_eq_zero_iff_eq_neg] at hx3AxB,
    have hB : (B : ℚ) ≠ 0 := λ hB, by { rw [hB] at hx3AxB, exact hx3Ax hx3AxB },
    have hpB : 0 ≤ (padic_val_int p B : ℤ) := int.coe_nat_nonneg _,
    apply_fun padic_val_rat p at hx3AxB,
    rw [hpx3Ax, padic_val_rat.pow p hx, padic_val_rat.neg, padic_val_rat.of_int] at hx3AxB,
    rw [← hx3AxB] at hpB,
    exact not_lt_of_le (nonneg_of_mul_nonneg_left hpB zero_lt_three) hpx
  end,
  have hpx3AxB : padic_val_rat p (x ^ 3 + A * x + B) = padic_val_rat p (x ^ 3) :=
  begin
    rw [← hpx3Ax],
    apply padic_val_rat.add_of_lt p hx3Ax,
    rw [hpx3Ax, padic_val_rat.pow p hx],
    by_cases hB : (B : ℚ) = 0,
    { simpa only [hB, padic_val_rat.zero] using mul_neg_of_pos_of_neg zero_lt_three hpx },
    rw [padic_val_rat.of_int],
    exact lt_of_lt_of_le (mul_neg_of_pos_of_neg zero_lt_three hpx) (int.coe_nat_nonneg _)
  end,
  have hy : y ≠ 0 := (pow_ne_zero_iff zero_lt_two).mp (w.symm ▸ hx3AxB),
  apply_fun padic_val_rat p at w,
  rw [padic_val_rat.pow p hy, hpx3AxB, padic_val_rat.pow p hx] at w,
  change 2 * padic_val_rat p y = 3 * padic_val_rat p x at w,
  cases int.dvd_of_dvd_mul_right_of_gcd_one (dvd.intro (padic_val_rat p y) w) (by norm_num1)
    with _ hn,
  rw [hn, ← mul_assoc, mul_comm (3 : ℤ), mul_assoc, mul_right_inj' $ @two_ne_zero ℤ _ _] at w,
  rw [hn] at hpx,
  rcases int.exists_eq_neg_of_nat (le_of_lt $ neg_of_mul_neg_left hpx zero_le_two) with ⟨n, rfl⟩,
  rw [mul_neg] at hn w,
  exact ⟨n, hn, w⟩
end

lemma y_of_x_neg (hpx : padic_val_rat p x < 0) : padic_val_rat p y < 0 :=
begin
  rcases of_x_neg w hpx with ⟨_, ⟨hx, hy⟩⟩,
  rw [hx, neg_neg_iff_pos] at hpx,
  rw [hy, neg_neg_iff_pos],
  exact mul_pos zero_lt_three ((pos_iff_pos_of_mul_pos hpx).mp zero_lt_two),
end

lemma x_neg_iff_y_neg : padic_val_rat p x < 0 ↔ padic_val_rat p y < 0 :=
⟨y_of_x_neg w, imp_of_not_imp_not _ _ $ not_lt_of_le ∘ y_of_x_nonneg w ∘ le_of_not_lt⟩

lemma x_neg_iff_y_neg' {p : ℕ} :
  p.prime ∧ padic_val_rat p x < 0 ↔ p.prime ∧ padic_val_rat p y < 0 :=
⟨λ ⟨hp, hpx⟩, ⟨hp, (@x_neg_iff_y_neg A B x y w p ⟨hp⟩).mp hpx⟩,
  λ ⟨hp, hpy⟩, ⟨hp, (@x_neg_iff_y_neg A B x y w p ⟨hp⟩).mpr hpy⟩⟩

/-- A prime of negative x valuation has negative y valuation. -/
def y_neg_of_x_neg :
  {p : ℕ // p.prime ∧ padic_val_rat p x < 0} → {p : ℕ // p.prime ∧ padic_val_rat p y < 0} :=
λ ⟨p, hp⟩, ⟨p, (x_neg_iff_y_neg' w).mp hp⟩

lemma y_neg_of_x_neg.bijective : function.bijective $ y_neg_of_x_neg w :=
⟨λ ⟨_, _⟩ ⟨_, _⟩ h, subtype.mk_eq_mk.mpr $ subtype.mk.inj_arrow h id,
  λ ⟨p, hp⟩, ⟨⟨p, (x_neg_iff_y_neg' w).mpr hp⟩, rfl⟩⟩

lemma x_denom_of_x_neg :
  (∀ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
    padic_val_rat p x = -(2 * (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some))
    → x.denom = ∏ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
                  (p : ℕ) ^ (2 * (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some) :=
begin
  intros hn,
  rw [← padic_val_rat.finprod_of_neg],
  apply fintype.prod_congr,
  rintro ⟨p, ⟨hp, hpx⟩⟩,
  congr' 1,
  change padic_val_nat p x.denom = _,
  rw [← int.coe_nat_inj', ← neg_inj, ← ((@padic_val_rat.eq_denom.tfae p ⟨hp⟩ x).out 2 0).mp $
        le_of_lt hpx],
  exact hn ⟨p, ⟨hp, hpx⟩⟩
end

lemma y_denom_of_x_neg :
  (∀ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
    padic_val_rat p y = -(3 * (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some))
    → y.denom = ∏ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
                  (p : ℕ) ^ (3 * (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some) :=
begin
  intros hn,
  rw [← padic_val_rat.finprod_of_neg],
  symmetry,
  apply fintype.prod_bijective (y_neg_of_x_neg w) (y_neg_of_x_neg.bijective w),
  rintro ⟨p, ⟨hp, hpx⟩⟩,
  symmetry,
  congr' 1,
  change padic_val_nat p y.denom = _,
  rw [← int.coe_nat_inj', ← neg_inj, ← ((@padic_val_rat.eq_denom.tfae p ⟨hp⟩ y).out 2 0).mp $
        le_of_lt $ (@x_neg_iff_y_neg A B x y w p ⟨hp⟩).mp hpx],
  exact hn ⟨p, ⟨hp, hpx⟩⟩
end

lemma denom_of_x_neg :
  x.denom = ∏ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
              (p : ℕ) ^ (2 * (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some)
  ∧ y.denom = ∏ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
                (p : ℕ) ^ (3 * (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some) :=
and.imp (x_denom_of_x_neg w) (y_denom_of_x_neg w) $ forall_and_distrib.mp $ λ ⟨p, ⟨hp, hpx⟩⟩,
  (@of_x_neg A B x y w p ⟨hp⟩ hpx).some_spec

lemma denom : ∃ n : ℕ, x.denom = n ^ 2 ∧ y.denom = n ^ 3 :=
⟨∏ p : {p : ℕ // p.prime ∧ padic_val_rat p x < 0},
  (p : ℕ) ^ (@of_x_neg A B x y w p ⟨p.property.1⟩ p.property.2).some,
  by simpa only [← finset.prod_pow, ← pow_mul'] using denom_of_x_neg w⟩

end padic_val_point

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## Heights -/

section heights

variables {E : EllipticCurve ℚ} {A B : ℤ}
variables (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0) (ha₄ : E.a₄ = A) (ha₆ : E.a₆ = B)

/-- The logarithmic height of a point on an elliptic curve over the rationals. -/
def height : E⟮ℚ⟯ → ℝ
| 0            := 0
| (some x _ _) := (max (|x.num|) (|x.denom|) : ℝ).log

@[simp] lemma height_zero : height (0 : E⟮ℚ⟯) = 0 := rfl

@[simp] lemma height_some {x y w} :
  height (some x y w : E⟮ℚ⟯) = (max (|x.num|) (|x.denom|) : ℝ).log :=
rfl

lemma height_nonneg (P : E⟮ℚ⟯) : 0 ≤ height P :=
begin
  cases P with x,
  { exact (le_refl 0) },
  { rw [height, real.le_log_iff_exp_le, real.exp_zero],
    all_goals { rw [nat.abs_cast] },
    rw [le_max_iff, nat.one_le_cast, nat.succ_le_iff],
    any_goals { rw [lt_max_iff, nat.cast_pos] },
    all_goals { exact or.inr x.pos } }
end

include ha₁ ha₃

def height_le_constant.function {C : ℝ} (hC : 0 ≤ C) :
  {P : E⟮ℚ⟯ // height P ≤ C} → option (fin (2 * ⌊C.exp⌋₊ + 1) × fin (⌊C.exp⌋₊ + 1) × fin 2)
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨(x.num + ⌊C.exp⌋).to_nat, x.denom, if y ≤ 0 then 0 else 1⟩

lemma height_le_constant.injective {C : ℝ} (hC : 0 ≤ C) :
  function.injective $ @height_le_constant.function E ha₁ ha₃ C hC :=
begin
  rintro ⟨_ | ⟨⟨n, d, hx, _⟩, y, w⟩, hP⟩ ⟨_ | ⟨⟨n', d', hx', _⟩, y', w'⟩, hQ⟩ hPQ,
  any_goals { contradiction },
  { refl },
  { rw [height_some, real.log_le_iff_le_exp, max_le_iff, abs_le'] at hP hQ,
    have hn : n ≤ ⌊C.exp⌋ ∧ n' ≤ ⌊C.exp⌋ := by { simp only [int.le_floor], exact ⟨hP.1.1, hQ.1.1⟩ },
    have hn' : 0 ≤ n + ⌊C.exp⌋ ∧ 0 ≤ n' + ⌊C.exp⌋ :=
    by { simp only [← neg_le_iff_add_nonneg', int.le_floor, int.cast_neg], exact ⟨hP.1.2, hQ.1.2⟩ },
    have hd : d < ⌊C.exp⌋₊ + 1 ∧ d' < ⌊C.exp⌋₊ + 1 :=
    by { simp only [nat.lt_add_one_iff, nat.le_floor_iff (le_of_lt $ C.exp_pos)],
         rw [← nat.abs_cast d, ← nat.abs_cast d'], exact ⟨hP.2, hQ.2⟩ },
    simp only [height_le_constant.function, prod.mk.inj_iff, fin.eq_iff_veq] at hPQ,
    rcases hPQ with ⟨hnn, hdd, hyy⟩,
    replace hnn : n = n' :=
    begin
      rw [fin.coe_val_of_lt, fin.coe_val_of_lt, ← int.of_nat.inj_eq, int.of_nat_eq_coe,
          int.to_nat_of_nonneg hn'.1, int.of_nat_eq_coe, int.to_nat_of_nonneg hn'.2,
          add_right_cancel_iff] at hnn,
      { exact hnn },
      all_goals { rw [nat.lt_add_one_iff, int.to_nat_le, int.coe_nat_mul, ← int.nat_cast_eq_coe_nat,
                      nat.cast_two, nat.cast_floor_eq_int_floor $ le_of_lt $ C.exp_pos, two_mul,
                      add_le_add_iff_right] },
      { exact hn.2 },
      { exact hn.1 }
    end,
    replace hdd : d = d' := by rwa [← fin.coe_val_of_lt hd.1, ← fin.coe_val_of_lt hd.2],
    replace hyy : y = y' :=
    begin
      simp only [ha₁, ha₃, map_zero, zero_mul, add_zero, ← hnn, ← hdd] at w w',
      rw [← w', sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at w,
      split_ifs at hyy with hy hy' hy',
      { rcases w with rfl | rfl,
        { refl },
        { rcases antisymm hy' (nonneg_of_neg_nonpos hy) with rfl,
          refl } },
      { exact false.elim (zero_ne_one hyy) },
      { exact false.elim (zero_ne_one hyy.symm) },
      { rcases w with rfl | rfl,
        { refl },
        { rcases antisymm (le_of_not_le hy') (nonpos_of_neg_nonneg $ le_of_not_le hy) with rfl,
          refl } }
    end,
    { simp only,
      exact ⟨⟨hnn, hdd⟩, hyy⟩ },
    any_goals { rw [lt_max_iff, nat.abs_cast, nat.cast_pos] },
    { exact or.inr hx },
    { exact or.inr hx' } }
end

instance height_le_constant.fintype (C : ℝ) : fintype {P : E⟮ℚ⟯ // height P ≤ C} :=
begin
  by_cases hC : 0 ≤ C,
  { exact fintype.of_injective (height_le_constant.function ha₁ ha₃ hC)
      (height_le_constant.injective ha₁ ha₃ hC) },
  { exact @fintype.of_is_empty {P : E⟮ℚ⟯ // height P ≤ C}
      ⟨λ ⟨P, hP⟩, hC $ le_trans (height_nonneg P) hP⟩ }
end

include ha₂ ha₄ ha₆

lemma exists_constant_height_add_le_two_mul_height_add_constant (Q : E⟮ℚ⟯) :
  ∃ C : ℝ, ∀ P : E⟮ℚ⟯, height (P + Q) ≤ 2 * height P + C :=
begin
  cases Q with x' y' w',
  { exact ⟨0, λ P, by simpa only [EllipticCurve.zero_def, add_zero, two_mul]
                      using le_add_of_nonneg_left (height_nonneg P)⟩ },
  { let hQ : ℝ := height (some x' y' w'),
    let h2Q : ℝ := height (EllipticCurve.dbl $ some x' y' w'),
    -- let C₁ : ℝ := (1 + |A| + |B| : ℝ).sqrt,
    -- let C₂ : ℝ := 1 + |x'|,
    -- let C₃ : ℝ := (|A| + |x'|) * C₂ + 2 * (|B| + |y'| * C₁),
    existsi [max 0 $ max hQ h2Q],
    rintro (_ | ⟨x, y, w⟩),
    { rw [EllipticCurve.zero_def, zero_add, height_zero, mul_zero, zero_add],
      exact le_max_of_le_right (le_max_left hQ h2Q) },
    { unfold has_add.add,
      unfold EllipticCurve.add,
      simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply, zero_mul,
                 add_zero] at w w',
      simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply, mul_zero,
                 zero_mul, add_zero, sub_zero] at *,
      split_ifs with hx hy,
      { sorry },
      { rw [not_ne_iff, eq_comm] at hx,
        subst hx,
        rw [← w', sq_eq_sq_iff_abs_eq_abs, abs_eq_abs,
            or_iff_left $ (not_iff_not_of_iff add_eq_zero_iff_eq_neg).mp hy, eq_comm] at w,
        subst w,
        exact le_add_of_nonneg_of_le (mul_nonneg zero_le_two $ height_nonneg _)
          (le_max_of_le_right $ le_max_right hQ h2Q) },
      all_goals { exact add_nonneg (mul_nonneg zero_le_two $ height_nonneg _)
                    (le_max_of_le_left $ le_refl 0) } } }
end

lemma exists_constant_four_mul_height_le_height_two_smul_add_constant :
  ∃ C : ℝ, ∀ P : E⟮ℚ⟯, 4 * height P ≤ height (EllipticCurve.dbl P) + C :=
begin
  let h2 : ℝ := 4 * finset.max'
    (finset.image (λ p : E⟮ℚ⟯[2], height p.val) (set.finite.of_fintype set.univ).to_finset)
    (by simp only [finset.nonempty.image_iff, set.finite.to_finset.nonempty, set.univ_nonempty]),
  -- let C₁ : ℝ := (max 12 $ 16 * |A|),
  -- let C₂ : ℝ := (max 3 $ max (5 * |A|) $ 27 * |B|),
  -- let C₃ : ℝ := (max (16 * |A| ^ 3 + 108 * B ^ 2) $ max (4 * A ^ 2 * |B|) $
  --                max (12 * A ^ 4 + 88 * |A| * B ^ 2) $ 12 * |A| ^ 3 * |B| + 96 * |B| ^ 3),
  -- let C₄ : ℝ := (max (A ^ 2 * |B|) $ max (5 * A ^ 4 + 32 * |A| * B ^ 2) $
  --                max (26 * |A| ^ 3 * |B| + 192 * |B| ^ 3) $ 3 * |A| ^ 5 + 24 * A ^ 2 * B ^ 2),
  existsi [max 0 h2],
  rintro (_ | ⟨x, y, w⟩),
  { rw [EllipticCurve.zero_def, EllipticCurve.dbl_zero, height_zero, mul_zero, zero_add],
    exact le_max_of_le_left (le_refl 0) },
  { unfold EllipticCurve.dbl,
    simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply, zero_mul, add_zero]
      at w,
    simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply, mul_zero, zero_mul,
               add_zero, sub_zero] at *,
    split_ifs with hy,
    { sorry },
    { sorry } }
end

end heights

end EllipticCurve

/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import number_theory.padics.padic_val
import analysis.special_functions.log.basic

import algebraic_geometry.EllipticCurve.torsion

/-!
# Heights on an elliptic curve over the rationals
-/

noncomputable theory
open_locale big_operators classical

----------------------------------------------------------------------------------------------------
/-! ## Lemmas -/

lemma int.coe_nat_max {m n : ℕ} : ((max m n : ℕ) : ℤ) = max m n :=
by simpa only [← int.nat_cast_eq_coe_nat] using nat.cast_max

lemma zero_le_three {α : Type} [ordered_semiring α] : (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

lemma zero_le_four {α : Type} [ordered_semiring α] : (0 : α) ≤ 4 :=
add_nonneg zero_le_two zero_le_two

lemma max_pow {α : Type} [linear_ordered_semiring α] {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
  max a b ^ n = max (a ^ n) (b ^ n) :=
begin
  by_cases hab : a ≤ b,
  { rw [max_eq_right hab, max_eq_right $ pow_le_pow_of_le_left ha hab n] },
  { rw [max_eq_left $ le_of_not_le hab,
        max_eq_left $ pow_le_pow_of_le_left hb (le_of_not_le hab) n] }
end

namespace padic_val_nat

variables (n : ℕ)

/-- A factor is a prime of non-zero valuation. -/
def ne_zero_of_factorization :
  n.factorization.support → {p : ℕ // p.prime ∧ padic_val_nat p n ≠ 0} :=
λ ⟨p, hp⟩, ⟨p, let hp' := nat.prime_of_mem_factorization hp in
  ⟨hp', (@padic_val_nat_eq_factorization p n ⟨hp'⟩).symm ▸ finsupp.mem_support_iff.mp hp⟩⟩

lemma ne_zero_of_factorization.bijective : function.bijective $ ne_zero_of_factorization n :=
⟨λ ⟨_, _⟩ ⟨_, _⟩ hp, subtype.mk_eq_mk.mpr $ subtype.mk.inj_arrow hp id, λ ⟨p, ⟨hp, hpn⟩⟩,
  ⟨⟨p, finsupp.mem_support_iff.mpr (@padic_val_nat_eq_factorization p n ⟨hp⟩ ▸ hpn)⟩, rfl⟩⟩

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
  have hy : y ≠ 0 := by { rintro rfl, rw [zero_pow two_pos] at w, exact hx3AxB w.symm },
  apply_fun padic_val_rat p at w,
  by_cases hx3Ax : x ^ 3 + A * x = 0,
  { rw [padic_val_rat.pow p hy, hx3Ax, zero_add, padic_val_rat.of_int] at w,
    exact (mul_nonneg_iff_right_nonneg_of_pos two_pos).mp (w.symm ▸ int.coe_nat_nonneg _) },
  have hx : x ≠ 0 :=
  begin
    rintro rfl,
    rw [zero_pow three_pos, zero_add, mul_zero] at hx3Ax,
    exact false_of_ne hx3Ax
  end,
  have hpx3 : 0 ≤ padic_val_rat p (x ^ 3) :=
  by simpa only [padic_val_rat.pow p hx]
     using (mul_nonneg_iff_right_nonneg_of_pos three_pos).mpr hpx,
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
  le_trans' (padic_val_rat.min_le_padic_val_rat_add p hx3AxB)
    (le_min (le_trans (le_min hpx3 hpAx) $ padic_val_rat.min_le_padic_val_rat_add p hx3Ax) hpB),
  rw [← w, padic_val_rat.pow p hy] at hpy2,
  exact nonneg_of_mul_nonneg_left hpy2 two_pos
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
    exact not_lt_of_le (nonneg_of_mul_nonneg_left hpA two_pos) hpx
  end,
  have hpx3Ax : padic_val_rat p (x ^ 3 + A * x) = padic_val_rat p (x ^ 3) :=
  begin
    apply padic_val_rat.add_of_lt p (pow_ne_zero 3 hx),
    rw [padic_val_rat.pow p hx],
    by_cases hA : (A : ℚ) = 0,
    { simpa only [hA, zero_mul, padic_val_rat.zero] using mul_neg_of_pos_of_neg three_pos hpx },
    rw [int.coe_nat_succ, add_mul, one_mul, padic_val_rat.mul p hA hx, add_lt_add_iff_right,
        padic_val_rat.of_int],
    exact lt_of_lt_of_le (mul_neg_of_pos_of_neg two_pos hpx) (int.coe_nat_nonneg _)
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
    exact not_lt_of_le (nonneg_of_mul_nonneg_left hpB three_pos) hpx
  end,
  have hpx3AxB : padic_val_rat p (x ^ 3 + A * x + B) = padic_val_rat p (x ^ 3) :=
  begin
    rw [← hpx3Ax],
    apply padic_val_rat.add_of_lt p hx3Ax,
    rw [hpx3Ax, padic_val_rat.pow p hx],
    by_cases hB : (B : ℚ) = 0,
    { simpa only [hB, padic_val_rat.zero] using mul_neg_of_pos_of_neg three_pos hpx },
    rw [padic_val_rat.of_int],
    exact lt_of_lt_of_le (mul_neg_of_pos_of_neg three_pos hpx) (int.coe_nat_nonneg _)
  end,
  have hy : y ≠ 0 := ne_zero_pow two_ne_zero (w.symm ▸ hx3AxB),
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
  exact mul_pos three_pos ((pos_iff_pos_of_mul_pos hpx).mp two_pos),
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

variables {E : EllipticCurve ℚ}

section height_def

/-- The logarithmic height of a point on an elliptic curve over the rationals. -/
def height : E⟮ℚ⟯ → ℝ
| 0            := 0
| (some x _ _) := (max (|x.num|) (|x.denom|) : ℝ).log

@[simp] lemma height_zero : height (0 : E⟮ℚ⟯) = 0 := rfl

@[simp] lemma height_some {x y w} :
  height (some x y w : E⟮ℚ⟯) = (max (|x.num|) (|x.denom|) : ℝ).log :=
rfl

lemma height_pos' (x : ℚ) : 0 < max (|x.num|) (|x.denom|) :=
lt_max_of_lt_right $ abs_pos_of_pos $ int.coe_nat_pos.mpr x.pos

lemma height_pos (x : ℚ) : (0 : ℝ) < max (|x.num|) (|x.denom|) :=
by simpa only [← @int.cast_pos ℝ] with push_cast using height_pos' x

lemma height_nonneg (P : E⟮ℚ⟯) : 0 ≤ height P :=
begin
  cases P with x,
  { exact (le_refl 0) },
  { rw [height_some, real.le_log_iff_exp_le $ height_pos x, real.exp_zero, nat.abs_cast],
    exact le_max_of_le_right (nat.one_le_cast.mpr $ nat.succ_le_of_lt x.pos) }
end

end height_def

section height_le

private def height_le_constant.function {C : ℝ} :
  {P : E⟮ℚ⟯ // height P ≤ C} → option (fin (2 * ⌊C.exp⌋₊ + 1) × fin (⌊C.exp⌋₊ + 1) × fin 2)
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨(x.num + ⌊C.exp⌋).to_nat, x.denom, if y ≤ 0 then 0 else 1⟩

variables {A B : ℤ} (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)

include ha₁ ha₃

private lemma height_le_constant.injective {C : ℝ} :
  function.injective $ @height_le_constant.function E C :=
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

/-- There are finitely many points of bounded height. -/
def height_le_constant.fintype (C : ℝ) : fintype {P : E⟮ℚ⟯ // height P ≤ C} :=
fintype.of_injective height_le_constant.function $ height_le_constant.injective ha₁ ha₃

end height_le

section height_add

variables (A B : ℤ) (x y : ℚ) (d : ℕ)

private def C₀ : ℝ := (1 + |A| + |B| : ℝ).sqrt
private def C₁ : ℤ := x.num * d ^ 2
private def C₂ : ℤ := x.num ^ 2 + A * (d ^ 2) ^ 2
private def C₃ : ℤ := A * x.num * d ^ 2 + 2 * B * (d ^ 2) ^ 2
private def C₄ : ℤ := 2 * y.num * d
private def C₅ : ℤ := (d ^ 2) ^ 2
private def C₆ : ℤ := 2 * x.num * d ^ 2
private def C₇ : ℤ := x.num ^ 2
private def R₁ : ℝ := |C₁ x d| + |C₂ A x d| + |C₃ A B x d| + C₀ A B * |C₄ y d|
private def R₂ : ℝ := |C₅ d| + |C₆ x d| + |C₇ x|

variables {A B x y d} {x' y' : ℚ} {d' : ℕ}

private lemma d_ne_zero (hxd : x.denom = d ^ 2) : (d : ℚ) ≠ 0 :=
by { rw [nat.cast_ne_zero], rintro rfl, exact ne_zero_of_lt x.pos hxd }

private lemma xd_ne_zero (hxd : x.denom = d ^ 2) (hxd' : x'.denom = d' ^ 2) (hx : x ≠ x') :
  x.num * (d' : ℤ) ^ 2 - (d : ℤ) ^ 2 * x'.num ≠ 0 :=
begin
  rw [← sub_ne_zero, ← rat.num_div_denom x, hxd, nat.cast_pow, ← rat.num_div_denom x', hxd',
      nat.cast_pow, div_sub_div _ _ (pow_ne_zero 2 $ d_ne_zero hxd) $
        pow_ne_zero 2 $ d_ne_zero hxd', div_ne_zero_iff] at hx,
  simpa only [← @int.cast_ne_zero ℚ] with push_cast using hx.1
end

private lemma C_pos (hxd : x.denom = d ^ 2) : 0 < max (R₁ A B x y d) (R₂ x d) :=
begin
  have hd : ((d : ℚ) : ℝ) ≠ 0 := rat.cast_ne_zero.mpr (d_ne_zero hxd),
  rw [rat.cast_coe_nat, ← @pow_ne_zero_iff ℝ _ _ _ _ two_pos, ← nat.cast_pow,
      ← @pow_ne_zero_iff ℝ _ _ _ _ two_pos, ← nat.cast_pow, ← abs_pos] at hd,
  exact lt_max_of_lt_right
    (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hd $ abs_nonneg _) $ abs_nonneg _)
end

private lemma add_rw (w : y ^ 2 = x ^ 3 + A * x + B) (w' : y' ^ 2 = x' ^ 3 + A * x' + B)
  (hxd : x.denom = d ^ 2) (hyd : y.denom = d ^ 3) (hxd' : x'.denom = d' ^ 2)
  (hyd' : y'.denom = d' ^ 3) (hx : x ≠ x') : ((y - y') * (x - x')⁻¹) ^ 2 - x - x' = rat.mk
    (x.num ^ 2 * C₁ x' d' + x.num * d ^ 2 * C₂ A x' d' + (d ^ 2) ^ 2 * C₃ A B x' d'
      - y.num * d * C₄ y' d')
    ((x.num * d' ^ 2 - d ^ 2 * x'.num) ^ 2) :=
calc ((y - y') * (x - x')⁻¹) ^ 2 - x - x'
      = (x ^ 3 + A * x + B - 2 * y * y' + (x' ^ 3 + A * x' + B) - (x + x') * (x - x') ^ 2)
        / (x - x') ^ 2 :
        by rw [← div_eq_mul_inv, div_pow, sub_sq, w, w', sub_sub, ← div_sub_div_same,
                mul_div_cancel _ $ pow_ne_zero 2 $ sub_ne_zero_of_ne hx]
  ... = (x.num ^ 2 * C₁ x' d' * (d ^ 2 / d ^ 2) ^ 2 * (d' ^ 2 / d' ^ 2)
          + x.num * d ^ 2 * (x'.num ^ 2 * (d' ^ 2 / d' ^ 2) ^ 2 + A * (d' ^ 2) ^ 2)
            * (d ^ 2 / d ^ 2)
          + (d ^ 2) ^ 2 * (A * x'.num * d' ^ 2 * (d' ^ 2 / d' ^ 2) + 2 * B * (d' ^ 2) ^ 2)
          - y.num * d * C₄ y' d' * (d ^ 3 / d ^ 3) * (d' ^ 3 / d' ^ 3))
        / (x.num * d' ^ 2 - d ^ 2 * x'.num) ^ 2 :
        begin
          conv_lhs { rw [← rat.num_div_denom x, hxd, ← rat.num_div_denom y, hyd,
                          ← rat.num_div_denom x', hxd', ← rat.num_div_denom y', hyd'] },
          push_cast [C₁, C₄],
          nth_rewrite_lhs 1 [div_sub_div _ _ (pow_ne_zero 2 $ d_ne_zero hxd) $
                               pow_ne_zero 2 $ d_ne_zero hxd'],
          rw [div_pow _ (d ^ 2 * d' ^ 2 : ℚ), div_div_eq_mul_div],
          ring1
        end
  ... = rat.mk
          (x.num ^ 2 * C₁ x' d' + x.num * d ^ 2 * C₂ A x' d' + (d ^ 2) ^ 2 * C₃ A B x' d'
            - y.num * d * C₄ y' d')
          ((x.num * d' ^ 2 - d ^ 2 * x'.num) ^ 2) :
        by push_cast [C₁, C₂, C₃, C₄, div_self (pow_ne_zero _ $ d_ne_zero hxd),
                      div_self (pow_ne_zero _ $ d_ne_zero hxd'), mul_one, one_pow, rat.mk_eq_div]

private lemma w_le (w : y ^ 2 = x ^ 3 + A * x + B) (hxd : x.denom = d ^ 2) (hyd : y.denom = d ^ 3) :
  (|y.num| * |d| : ℝ) ≤ max (|x.num|) (|d ^ 2|) ^ 2 * C₀ A B :=
begin
  have y_eq : (y.num ^ 2 : ℚ) = x.num ^ 3 + x.num * (d ^ 2) ^ 2 * A + (d ^ 2) ^ 3 * B :=
  begin
    conv_lhs { rw [← div_mul_cancel (y.num : ℚ) $ pow_ne_zero 3 $ d_ne_zero hxd, mul_pow, ← pow_mul,
                   ← nat.cast_pow, ← hyd, rat.num_div_denom, w, ← rat.num_div_denom x, hxd,
                   nat.cast_pow, div_pow, add_mul, add_mul, pow_mul',
                   div_mul_cancel (x.num ^ 3 : ℚ) $ pow_ne_zero 3 $ pow_ne_zero 2 $ d_ne_zero hxd,
                   pow_succ (d ^ 2 : ℚ), ← mul_assoc, mul_assoc (A : ℚ),
                   div_mul_cancel (x.num : ℚ) $ pow_ne_zero 2 $ d_ne_zero hxd] },
    ring1
  end,
  have y_le : (|y.num| : ℝ) ≤ max (|x.num| : ℝ).sqrt (|d|) ^ 3 * C₀ A B :=
  begin
    push_cast [← @rat.cast_inj ℝ] at y_eq,
    rw [← real.sqrt_sq $ abs_nonneg _, pow_abs, y_eq,
        ← real.sqrt_sq $ pow_nonneg (le_max_of_le_right $ abs_nonneg _) 3, ← pow_mul _ 3,
        max_pow (real.sqrt_nonneg _) $ abs_nonneg _, pow_mul', real.sq_sqrt $ abs_nonneg _,
        pow_mul', C₀, ← real.sqrt_mul $ le_max_of_le_left $ pow_nonneg (abs_nonneg _) 3],
    apply real.sqrt_le_sqrt (le_trans' _ $ abs_add_three _ _ _),
    simp only [abs_mul, abs_pow, mul_add, mul_one],
    apply add_le_add_three,
    { exact le_max_left _ _ },
    { refine mul_le_mul_of_nonneg_right _ (abs_nonneg _),
      by_cases hsq : (|x.num| : ℝ) ≤ |d| ^ 2,
      { apply le_trans (mul_le_mul_of_nonneg_right hsq $ sq_nonneg _),
        simpa only [← pow_succ] using le_max_right _ _ },
      { refine le_trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_left (sq_nonneg _) (le_of_lt $ lt_of_not_le hsq) 2) $
            abs_nonneg _) _,
        simpa only [← pow_succ] using le_max_left _ _ } },
    { exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _) }
  end,
  have d_le : (|d| : ℝ) * max (|x.num| : ℝ).sqrt (|d|) ^ 3 ≤ max (|x.num|) (|↑d ^ 2|) ^ 2 :=
  begin
    by_cases hsq : (|x.num| : ℝ) ≤ |d ^ 2|,
    { rw [max_eq_right hsq],
      rw [← real.sqrt_le_sqrt_iff $ abs_nonneg _, abs_pow, real.sqrt_sq $ abs_nonneg _] at hsq,
      simpa only [max_eq_right hsq, ← pow_succ, abs_pow, ← pow_mul] using le_refl _ },
    { rw [max_eq_left_of_lt $ lt_of_not_le hsq],
      nth_rewrite_rhs 0 [← real.sq_sqrt $ abs_nonneg _],
      rw [not_le, ← real.sqrt_lt_sqrt_iff $ abs_nonneg _, abs_pow, real.sqrt_sq $ abs_nonneg _]
        at hsq,
      apply le_trans
        (mul_le_mul_of_nonneg_right (le_of_lt hsq) $
          pow_nonneg (le_max_of_le_right $ abs_nonneg _) 3),
      simpa only [max_eq_left_of_lt hsq, ← pow_succ, ← pow_mul] using le_refl _ }
  end,
  apply le_trans (mul_le_mul_of_nonneg_right y_le $ abs_nonneg _),
  rw [mul_comm, ← mul_assoc],
  exact mul_le_mul_of_nonneg_right d_le (real.sqrt_nonneg _)
end

variables (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0) (ha₄ : E.a₄ = A) (ha₆ : E.a₆ = B)

include ha₁ ha₂ ha₃ ha₄ ha₆

lemma exists_constant_height_add_le (Q : E⟮ℚ⟯) :
  ∃ C : ℝ, ∀ P : E⟮ℚ⟯, height (P + Q) ≤ 2 * height P + C :=
begin
  cases Q with x' y' w',
  { exact ⟨0, λ P, by simpa only [EllipticCurve.zero_def, add_zero, two_mul]
                      using le_add_of_nonneg_left (height_nonneg P)⟩ },
  { have sw' := w',
    simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply, zero_mul, add_zero]
      at sw',
    rcases padic_val_point.denom sw' with ⟨d', hxd', hyd'⟩,
    existsi [max (height $ some x' y' w') $ max (height $ EllipticCurve.dbl $ some x' y' w') $
             real.log $ max (R₁ A B x' y' d') $ R₂ x' d'],
    rintro (_ | ⟨x, y, w⟩),
    { simpa only [EllipticCurve.zero_def, zero_add, height_zero, mul_zero] using le_max_left _ _ },
    { have sw := w,
      conv_lhs { dsimp only [has_add.add] },
      unfold EllipticCurve.add,
      simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply, mul_zero,
                 zero_mul, add_zero, sub_zero] at sw ⊢,
      split_ifs with hx hy,
      { by_cases hxy : ((y - y') * (x - x')⁻¹) ^ 2 - x - x' = 0,
        { rw [height_some, hxy, rat.num_zero, int.cast_zero, abs_zero, rat.denom_zero, nat.cast_one,
              abs_one, max_eq_right $ @zero_le_one ℝ _, real.log_one],
          exact le_add_of_nonneg_of_le (mul_nonneg zero_le_two $ height_nonneg _)
            (le_max_of_le_left $ height_nonneg _) },
        rcases padic_val_point.denom sw with ⟨d, hxd, hyd⟩,
        refine le_trans _ (add_le_add_left (le_max_of_le_right $ le_max_right _ _) _),
        nth_rewrite_rhs 0 [← nat.cast_two],
        rw [height_some, real.log_le_iff_le_exp $ height_pos _, real.exp_add, real.exp_nat_mul,
            height_some, real.exp_log $ height_pos _, real.exp_log $ C_pos hxd', max_le_iff],
        split,
        { apply le_trans' ((mul_le_mul_left $ pow_pos (height_pos _) 2).mpr $ le_max_left _ _),
          rw [hxd, nat.cast_pow],
          calc (|(((y - y') * (x - x')⁻¹) ^ 2 - x - x').num| : ℝ)
                ≤ (|x.num ^ 2 * C₁ x' d' + x.num * d ^ 2 * C₂ A x' d' + (d ^ 2) ^ 2 * C₃ A B x' d'
                    - y.num * d * C₄ y' d'| : ℤ) :
                  by simpa only [← int.cast_abs, int.cast_le, add_rw sw sw' hxd hyd hxd' hyd' hx]
                     using int.le_of_dvd
                       (abs_pos.mpr $ rat.mk_num_ne_zero_of_ne_zero hxy $
                         add_rw sw sw' hxd hyd hxd' hyd' hx)
                       ((abs_dvd_abs _ _).mpr $ rat.num_dvd _ $ pow_ne_zero 2 $
                         xd_ne_zero hxd hxd' hx)
            ... ≤ |x.num| ^ 2 * |C₁ x' d'| + |x.num| * |d ^ 2| * |C₂ A x' d'|
                  + |d ^ 2| ^ 2 * |C₃ A B x' d'| + |y.num| * |d| * |C₄ y' d'| :
                  by simpa only [int.cast_le, ← abs_mul, pow_abs] with push_cast
                     using le_trans (abs_sub _ _) (add_le_add_right (abs_add_three _ _ _) _)
            ... ≤ max (|x.num|) (|d ^ 2|) ^ 2 * R₁ A B x' y' d' :
                  begin
                    simp only [R₁, mul_add, ← mul_assoc],
                    apply add_le_add,
                    { apply add_le_add_three,
                      { exact mul_le_mul_of_nonneg_right
                          (pow_le_pow_of_le_left (abs_nonneg _) (le_max_left _ _) 2)
                          (abs_nonneg _) },
                      { rw [sq $ max _ _],
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul (le_max_left _ _) (le_max_right _ _) (abs_nonneg _) $
                            le_max_of_le_left $ abs_nonneg _) (abs_nonneg _) },
                      { exact mul_le_mul_of_nonneg_right
                          (pow_le_pow_of_le_left (abs_nonneg _) (le_max_right _ _) 2)
                          (abs_nonneg _) } },
                    { exact mul_le_mul_of_nonneg_right (w_le sw hxd hyd) (abs_nonneg _) }
                  end },
        { apply le_trans' ((mul_le_mul_left $ pow_pos (height_pos _) 2).mpr $ le_max_right _ _),
          rw [hxd, nat.cast_pow],
          calc (|(((y - y') * (x - x')⁻¹) ^ 2 - x - x').denom| : ℝ)
                ≤ (|(x.num * d' ^ 2 - d ^ 2 * x'.num) ^ 2| : ℤ) :
                  by simpa only [← int.cast_coe_nat, ← int.cast_abs, int.cast_le,
                                 add_rw sw sw' hxd hyd hxd' hyd' hx]
                     using int.le_of_dvd (abs_pos.mpr $ pow_ne_zero 2 $ xd_ne_zero hxd hxd' hx)
                       ((abs_dvd_abs _ _).mpr $ rat.denom_dvd _ _)
            ... ≤ |x.num ^ 2 * C₅ d' - x.num * d ^ 2 * C₆ x' d' + (d ^ 2) ^ 2 * C₇ x'| :
                  le_of_eq $ by { push_cast [C₅, C₆, C₇], congr' 1, ring1 }
            ... ≤ |x.num| ^ 2 * |C₅ d'| + |x.num| * |d ^ 2| * |C₆ x' d'| + |d ^ 2| ^ 2 * |C₇ x'| :
                  by simpa only [← abs_mul, pow_abs]
                     using le_trans (abs_add _ _) (add_le_add_right (abs_sub _ _) _)
            ... ≤ max (|x.num|) (|d ^ 2|) ^ 2 * R₂ x' d' :
                  begin
                    simp only [R₂, mul_add],
                    apply add_le_add_three,
                    { exact mul_le_mul_of_nonneg_right
                        (pow_le_pow_of_le_left (abs_nonneg _) (le_max_left _ _) 2) (abs_nonneg _) },
                    { rw [sq $ max _ _],
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul (le_max_left _ _) (le_max_right _ _) (abs_nonneg _) $
                          le_max_of_le_left $ abs_nonneg _) (abs_nonneg _) },
                    { exact mul_le_mul_of_nonneg_right
                        (pow_le_pow_of_le_left (abs_nonneg _) (le_max_right _ _) 2) (abs_nonneg _) }
                  end } },
      { rw [not_ne_iff, eq_comm] at hx,
        subst hx,
        rw [← sw', sq_eq_sq_iff_abs_eq_abs, abs_eq_abs,
            or_iff_left $ (not_iff_not_of_iff add_eq_zero_iff_eq_neg).mp hy, eq_comm] at sw,
        subst sw,
        exact le_add_of_nonneg_of_le (mul_nonneg zero_le_two $ height_nonneg _)
          (le_max_of_le_right $ le_max_left _ _) },
      all_goals { exact add_nonneg (mul_nonneg zero_le_two $ height_nonneg _)
                    (le_max_of_le_left $ height_nonneg _) } } }
end

end height_add

section height_dbl

variables (A B a b : ℤ)

private def Δ : ℤ := 4 * A ^ 3 + 27 * B ^ 2
private def F : ℤ := a ^ 4 - 2 * A * a ^ 2 * b ^ 2 - 8 * B * a * b ^ 3 + A ^ 2 * b ^ 4
private def G : ℤ := 4 * (a ^ 3 * b + A * a * b ^ 3 + B * b ^ 4)
private def f₁ : ℤ := 12 * (a ^ 2 * b) + 16 * A * b ^ 3
private def g₁ : ℤ := 3 * a ^ 3 - 5 * A * (a * b ^ 2) - 27 * B * b ^ 3
private def f₂ : ℤ :=
4 * (4 * A ^ 3 + 27 * B ^ 2) * a ^ 3 - 4 * A ^ 2 * B * (a ^ 2 * b)
  + 4 * A * (3 * A ^ 3 + 22 * B ^ 2) * (a * b ^ 2)
  + 12 * B * (A ^ 3 + 8 * B ^ 2) * b ^ 3
private def g₂ : ℤ :=
-A ^ 2 * B * a ^ 3 - A * (5 * A ^ 3 + 32 * B ^ 2) * (a ^ 2 * b)
  - 2 * B * (13 * A ^ 3 + 96 * B ^ 2) * (a * b ^ 2)
  + 3 * A ^ 2 * (A ^ 3 + 8 * B ^ 2) * b ^ 3
private def f₁' : ℤ := |12| + |16 * A|
private def g₁' : ℤ := |3| + |5 * A| + |27 * B|
private def f₂' : ℤ :=
|4 * (4 * A ^ 3 + 27 * B ^ 2)| + |4 * A ^ 2 * B| + |4 * A * (3 * A ^ 3 + 22 * B ^ 2)|
  + |12 * B * (A ^ 3 + 8 * B ^ 2)|
private def g₂' : ℤ :=
|(-A ^ 2 * B)| + |A * (5 * A ^ 3 + 32 * B ^ 2)| + |2 * B * (13 * A ^ 3 + 96 * B ^ 2)|
  + |3 * A ^ 2 * (A ^ 3 + 8 * B ^ 2)|
private def C : ℤ := max (max (f₁' A) $ g₁' A B) (max (f₂' A B) $ g₂' A B)

variables {A B a b} {x y : ℚ}

private lemma denom_ne_zero : (x.denom : ℚ) ≠ 0 := nat.cast_ne_zero.mpr $ ne_zero_of_lt x.pos

private lemma x_mul_denom :
  (x ^ 3 + A * x + B) * x.denom ^ 4
    = x.num ^ 3 * x.denom + A * x.num * x.denom ^ 3 + B * x.denom ^ 4 :=
begin
  conv_lhs { congr, rw [← rat.num_div_denom x, div_pow, mul_div_assoc'], skip, rw [pow_succ] },
  rw [add_mul, add_mul, ← mul_assoc, ← mul_div_right_comm, div_mul_cancel _ $
        pow_ne_zero 3 denom_ne_zero, ← mul_assoc, div_mul_cancel _ denom_ne_zero, ← pow_succ]
end

private lemma C_pos : 0 < C A B :=
lt_max_of_lt_left $ lt_max_of_lt_left $
  add_pos_of_pos_of_nonneg (abs_pos_of_pos $ bit0_pos $ bit0_pos three_pos) $ abs_nonneg _

private lemma x_ne_zero (w : y ^ 2 = x ^ 3 + A * x + B) (hy : 2 * y ≠ 0) :
  2 ^ 2 * (x ^ 3 + A * x + B) ≠ 0 :=
mul_ne_zero (pow_ne_zero 2 $ two_ne_zero) $ w ▸ pow_ne_zero 2 $ right_ne_zero_of_mul hy

private lemma G_ne_zero (w : y ^ 2 = x ^ 3 + A * x + B) (hy : 2 * y ≠ 0) :
  G A B x.num x.denom ≠ 0 :=
begin
  have hx : (x ^ 3 + A * x + B) * x.denom ^ 4 ≠ 0 :=
  mul_ne_zero (right_ne_zero_of_mul $ x_ne_zero w hy) (pow_ne_zero 4 denom_ne_zero),
  rw [x_mul_denom] at hx,
  simpa only [G, ← @int.cast_ne_zero ℚ] with push_cast using mul_ne_zero four_ne_zero hx
end

private lemma dbl_rw (w : y ^ 2 = x ^ 3 + A * x + B) (hy : 2 * y ≠ 0) :
  ((3 * x ^ 2 + A) * (2 * y)⁻¹) ^ 2 - 2 * x = rat.mk (F A B x.num x.denom) (G A B x.num x.denom) :=
calc ((3 * x ^ 2 + A) * (2 * y)⁻¹) ^ 2 - 2 * x
      = ((3 * x ^ 2 + A) ^ 2 - 2 * x * (2 ^ 2 * (x ^ 3 + A * x + B)))
        / (2 ^ 2 * (x ^ 3 + A * x + B)) :
        by rw [← div_eq_mul_inv, div_pow, mul_pow, w, ← div_sub_div_same,
               mul_div_cancel _ $ x_ne_zero w hy]
  ... = (x ^ 4 - 2 * A * x ^ 2 - 8 * B * x + A ^ 2) / (4 * (x ^ 3 + A * x + B)) :
        by { norm_num1, ring1 }
  ... = (x.num ^ 4 * (x.denom ^ 4 / x.denom ^ 4)
          - 2 * A * x.num ^ 2 * x.denom ^ 2 * (x.denom ^ 2 / x.denom ^ 2)
          - 8 * B * x.num * x.denom ^ 3 * (x.denom / x.denom) + A ^ 2 * x.denom ^ 4)
        / (4 * (x.num ^ 3 * x.denom + A * x.num * x.denom ^ 3 + B * x.denom ^ 4)) :
        begin
          conv_lhs { rw [← mul_div_mul_right _ _ $ pow_ne_zero 4 denom_ne_zero], congr, congr,
                     rw [← rat.num_div_denom x, div_pow, div_pow], skip, skip,
                     rw [mul_assoc (4 : ℚ), x_mul_denom] },
          ring1
        end
  ... = rat.mk (F A B x.num x.denom) (G A B x.num x.denom) :
        by push_cast [F, G, div_self denom_ne_zero, div_self (pow_ne_zero _ denom_ne_zero), mul_one,
                      rat.mk_eq_div]

private lemma Δab_rw :
  f₂ A B a b * F A B a b - g₂ A B a b * G A B a b = 4 * Δ A B * a ^ 7
  ∧ f₁ A a b * F A B a b - g₁ A B a b * G A B a b = 4 * Δ A B * b ^ 7 :=
by { unfold Δ F G f₁ g₁ f₂ g₂, split, all_goals { ring1 } }

private lemma Δ_rw : (4 * Δ A B * x.num ^ 7).gcd (4 * Δ A B * x.denom ^ 7) = (4 * Δ A B).nat_abs :=
begin
  rw [int.gcd_mul_left, int.gcd_eq_one_iff_coprime.mpr, mul_one],
  exact is_coprime.pow (int.coprime_iff_nat_coprime.mpr x.cop)
end

private lemma Δab_le :
  max (|4 * Δ A B * a ^ 7|) (|4 * Δ A B * b ^ 7|)
    ≤ 2 * (max (max (|f₁ A a b|) $ |g₁ A B a b|) (max (|f₂ A B a b|) $ |g₂ A B a b|)
            * max (|F A B a b|) (|G A B a b|)) :=
begin
  rw [← Δab_rw.1, ← Δab_rw.2, max_mul_of_nonneg _ _ $ le_max_of_le_left $ abs_nonneg $ F A B a b,
      mul_max_of_nonneg _ _ zero_le_two, max_comm],
  apply max_le_max,
  all_goals { apply le_trans (abs_sub _ _),
              rw [abs_mul, abs_mul, two_mul],
              exact add_le_add
                (mul_le_mul (le_max_left _ _) (le_max_left _ _) (abs_nonneg _) $
                  le_max_of_le_left $ abs_nonneg _)
                (mul_le_mul (le_max_right _ _) (le_max_right _ _) (abs_nonneg _) $
                  le_max_of_le_left $ abs_nonneg _) }
end

private lemma fg_le :
  max (max (|f₁ A x.num x.denom|) $ |g₁ A B x.num x.denom|)
    (max (|f₂ A B x.num x.denom|) $ |g₂ A B x.num x.denom|)
    ≤ C A B * max (|x.num|) (|x.denom|) ^ 3 :=
begin
  simp only [C, f₁', g₁', f₂', g₂', add_mul,
             max_mul_of_nonneg _ _ (pow_nonneg (le_max_of_le_left $ abs_nonneg x.num) 3)],
  apply max_le_max,
  all_goals { apply max_le_max },
  any_goals { apply le_trans (abs_add _ _),
              conv_lhs { congr, rw [abs_mul, abs_mul, abs_pow], skip, rw [abs_mul, abs_pow] },
              apply add_le_add },
  any_goals { refine le_trans (abs_sub _ _) (le_trans (add_le_add_right (abs_sub _ _) _) _),
              conv_lhs { congr, congr, rw [abs_mul, abs_pow], skip,
                         rw [abs_mul, abs_mul x.num, abs_pow], skip, rw [abs_mul, abs_pow] },
              apply add_le_add_three },
  any_goals { refine le_trans (abs_add_three _ _ _)
                (le_trans (add_le_add_right (add_le_add_right (abs_sub _ _) _) _) _),
              conv_lhs { congr, congr, congr, rw [abs_mul, abs_pow], skip,
                         rw [abs_mul, abs_mul $ x.num ^ 2, abs_pow], skip,
                         rw [abs_mul, abs_mul x.num, abs_pow], skip, rw [abs_mul, abs_pow] },
              refine add_le_add_three (add_le_add _ _) _ _ },
  any_goals { refine le_trans (abs_add _ _)
                (le_trans (add_le_add_right (abs_sub _ _) _) $
                  le_trans (add_le_add_right (add_le_add_right (abs_sub _ _) _) _) _),
              conv_lhs { congr, congr, congr, rw [abs_mul, abs_pow], skip,
                         rw [abs_mul, abs_mul $ x.num ^ 2, abs_pow], skip,
                         rw [abs_mul, abs_mul x.num, abs_pow], skip, rw [abs_mul, abs_pow] },
              refine add_le_add_three (add_le_add _ _) _ _ },
  any_goals { exact mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_left (abs_nonneg _) (le_max_left _ _) 3) (abs_nonneg _) },
  any_goals { rw [pow_succ' $ max _ _],
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul (pow_le_pow_of_le_left (abs_nonneg _) (le_max_left _ _) 2)
                  (le_max_right _ _) (abs_nonneg _) $ sq_nonneg _) (abs_nonneg _) },
  any_goals { rw [pow_succ $ max _ _],
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul (le_max_left _ _)
                  (pow_le_pow_of_le_left (abs_nonneg _) (le_max_right _ _) 2) (sq_nonneg _) $
                  le_max_of_le_left $ abs_nonneg _) (abs_nonneg _) },
  any_goals { exact mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_left (abs_nonneg _) (le_max_right _ _) 3) (abs_nonneg _) }
end

variables (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0) (ha₄ : E.a₄ = A) (ha₆ : E.a₆ = B)

include ha₁ ha₂ ha₃ ha₄ ha₆

private lemma Δ_ne_zero : 4 * Δ A B ≠ 0 :=
begin
  push_cast [Δ, ← @int.cast_ne_zero ℚ],
  apply @right_ne_zero_of_mul _ _ (-4 : ℚ),
  convert_to E.disc_unit.val ≠ 0,
  { rw [E.disc_unit_eq, ha₁, ha₂, ha₃, ha₄, ha₆, disc_aux],
    ring1 },
  exact E.disc_unit.ne_zero
end

private lemma gcd_le (hy : 2 * y ≠ 0) :
  (F A B x.num x.denom).gcd (G A B x.num x.denom) ≤ (4 * Δ A B).nat_abs :=
begin
  apply nat.le_of_dvd (int.nat_abs_pos_of_ne_zero $ Δ_ne_zero ha₁ ha₂ ha₃ ha₄ ha₆),
  rw [← Δ_rw, ← Δab_rw.1, ← Δab_rw.2],
  apply nat.dvd_gcd,
  all_goals { exact int.dvd_nat_abs_of_of_nat_dvd
                (dvd_sub (dvd_mul_of_dvd_right (int.gcd_dvd_left _ _) _) $
                  dvd_mul_of_dvd_right (int.gcd_dvd_right _ _) _) }
end

private lemma FG_le (w : y ^ 2 = x ^ 3 + A * x + B) (hy : 2 * y ≠ 0) :
  max (|F A B x.num x.denom|) (|G A B x.num x.denom|)
    ≤ max (|(rat.mk (F A B x.num x.denom) $ G A B x.num x.denom).num|)
        (|(rat.mk (F A B x.num x.denom) $ G A B x.num x.denom).denom|) * |4 * Δ A B| :=
begin
  simp only [int.abs_eq_nat_abs, ← int.coe_nat_max],
  rw [← int.coe_nat_mul, int.coe_nat_le, ← nat.div_mul_cancel $ int.coe_nat_dvd_left.mp $
        int.gcd_dvd_left _ $ G A B x.num x.denom, ← nat.div_mul_cancel $ int.coe_nat_dvd_left.mp $
        int.gcd_dvd_right (F A B x.num x.denom) $ G _ _ _ _, ← max_mul_of_nonneg, rat.num_mk,
      int.nat_abs_div _ _ $ dvd_mul_of_dvd_right (int.gcd_dvd_left _ _) _,
      int.nat_abs_mul (G A B _ _).sign, int.nat_abs_sign, if_neg $ G_ne_zero w hy, one_mul,
      int.nat_abs_of_nat, int.nat_abs_of_nat, rat.denom_mk, if_neg $ G_ne_zero w hy],
  { exact nat.mul_le_mul_left _ (gcd_le ha₁ ha₂ ha₃ ha₄ ha₆ hy) },
  { exact zero_le _ }
end

lemma exists_constant_le_height_dbl :
  ∃ C : ℝ, ∀ P : E⟮ℚ⟯, 4 * height P ≤ height (EllipticCurve.dbl P) + C :=
begin
  existsi [max (4 * finset.max'
                (finset.image (λ p : E⟮ℚ⟯[2], height p.val)
                  (set.finite.of_fintype set.univ).to_finset)
                (by simp only [finset.nonempty.image_iff, set.finite.to_finset.nonempty,
                               set.univ_nonempty])) $
           real.log (2 * C A B : ℤ)],
  rintro (_ | ⟨x, y, w⟩),
  { rw [EllipticCurve.zero_def, EllipticCurve.dbl_zero, height_zero, mul_zero, zero_add],
    exact le_max_of_le_left
      (mul_nonneg zero_le_four $ finset.le_max' _ _ $ finset.mem_image.mpr
        ⟨⟨0, map_zero $ mul_by 2⟩, (set.finite.mem_to_finset _).mpr $ set.mem_univ _, rfl⟩) },
  { have sw := w,
    have E₂_y : y = 0 → some x y w ∈ E⟮ℚ⟯[2],
    any_goals { rintro rfl,
                rw [E₂_y, eq_inv_mul_iff_mul_eq₀ $ @two_ne_zero ℚ _ _, mul_zero, zero_eq_neg] },
    any_goals { unfold EllipticCurve.dbl },
    all_goals { simp only [ha₁, ha₂, ha₃, ha₄, ha₆, algebra_map_rat_rat, ring_hom.id_apply,
                           mul_zero, zero_mul, add_zero, sub_zero] at sw ⊢ },
    split_ifs with hy,
    { convert_to ((4 : ℕ) : ℝ) * _ ≤ _,
      { rw [nat.cast_bit0, nat.cast_two] },
      refine le_trans _ (add_le_add_left (le_max_right _ _) _),
      rw [height_some, ← real.log_pow, real.log_le_iff_le_exp $ pow_pos (height_pos _) 4,
          ← int.cast_coe_nat, ← int.cast_abs, ← int.cast_abs, ← int.cast_max, ← int.cast_pow,
          real.exp_add, height_some, real.exp_log $ height_pos _, dbl_rw sw hy, ← int.cast_coe_nat,
          ← int.cast_abs, ← int.cast_abs, ← int.cast_max, real.exp_log, ← int.cast_mul, int.cast_le,
          ← mul_le_mul_left $ pow_pos (height_pos' _) 3, ← pow_add,
          max_pow (abs_nonneg x.num) $ abs_nonneg _, pow_abs, pow_abs, mul_comm, mul_assoc,
          mul_assoc, mul_comm, ← mul_le_mul_left $ abs_pos.mpr $ Δ_ne_zero ha₁ ha₂ ha₃ ha₄ ha₆,
          mul_max_of_nonneg _ _ $ abs_nonneg $ 4 * Δ A B, ← abs_mul, ← abs_mul, mul_comm $ |_|,
          mul_assoc $ (2 : ℤ) * _, mul_assoc (2 : ℤ)],
      any_goals { exact int.cast_pos.mpr (mul_pos two_pos C_pos) },
      exact le_trans Δab_le
        (mul_le_mul_of_nonneg_left
          (mul_le_mul fg_le (FG_le ha₁ ha₂ ha₃ ha₄ ha₆ sw hy) (le_max_of_le_left $ abs_nonneg _) $
            le_of_lt $ mul_pos C_pos $ pow_pos (height_pos' _) 3)
          zero_le_two) },
    { rw [not_ne_iff, two_mul, add_self_eq_zero] at hy,
      subst hy,
      rw [height_zero, zero_add],
      exact le_max_of_le_left
        (mul_le_mul_of_nonneg_left
          (finset.le_max' _ _ $ finset.mem_image.mpr
            ⟨⟨some x 0 w, E₂_y rfl⟩, (set.finite.mem_to_finset _).mpr $ set.mem_univ _, rfl⟩)
          zero_le_four) } }
end

end height_dbl

end heights

end EllipticCurve

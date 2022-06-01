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
open_locale classical

----------------------------------------------------------------------------------------------------
/-! ## Lemmas -/

lemma zero_le_three {α : Type} [ordered_semiring α] : (0 : α) ≤ 3 :=
add_nonneg zero_le_two zero_le_one

namespace padic_val_rat

variables (p : ℕ) [fact p.prime]

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

lemma num_or_denom_eq_zero (q : ℚ) : padic_val_int p q.num = 0 ∨ padic_val_nat p q.denom = 0 :=
begin
  simp only [padic_val_int, padic_val_nat, multiplicity, enat.find_get],
  split_ifs,
  any_goals { simp only [nat.find_eq_zero, pow_one, eq_self_iff_true, or_true, true_or] },
  by_cases hdenom : p ∣ q.denom,
  { exact or.inl
      (λ hnum, nat.not_coprime_of_dvd_of_dvd (nat.prime.one_lt _inst_1.elim) hnum hdenom q.cop) },
  { exact or.inr hdenom }
end

lemma eq_zero (q : ℚ) :
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

lemma eq_num_tfae (q : ℚ) : tfae [padic_val_rat p q = padic_val_int p q.num,
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

lemma eq_denom_tfae (q : ℚ) : tfae [padic_val_rat p q = -padic_val_nat p q.denom,
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

end padic_val_rat

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## p-adic valuations of points -/

section padic_val_point

variables {A B : ℤ} {x y : ℚ} (w : y ^ 2 = x ^ 3 + A * x + B) {p : ℕ} [fact p.prime]

include w

lemma padic_val_point_of_x_nonneg (hpx : 0 ≤ padic_val_rat p x) : 0 ≤ padic_val_rat p y :=
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

lemma padic_val_point_of_x_neg (hpx : padic_val_rat p x < 0) :
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

end padic_val_point

----------------------------------------------------------------------------------------------------
/-! ## Heights -/

section heights

variables {E : EllipticCurve ℚ} {A B : ℤ}
variables (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0) (ha₄ : E.a₄ = A) (ha₆ : E.a₆ = B)

/-- The logarithmic height of a point on an elliptic curve over the rationals. -/
def height : E⟮ℚ⟯ → ℝ
| 0            := 0
| (some x _ _) := (max (|x.num|) (|x.denom|) : ℝ).log

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

def height_le_constant.function {C : ℝ} (hC : 0 ≤ C) : {P : E⟮ℚ⟯ // height P ≤ C}
  → option (fin (2 * ⌊C.exp⌋₊ + 1) × fin (⌊C.exp⌋₊ + 1) × fin 2)
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨(x.num + ⌊C.exp⌋).to_nat, x.denom, if y ≤ 0 then 0 else 1⟩

lemma height_le_constant.surjective {C : ℝ} (hC : 0 ≤ C) :
  function.injective $ @height_le_constant.function E ha₁ ha₃ C hC :=
begin
  rintro ⟨_ | ⟨⟨n, d, hx, _⟩, y, w⟩, hP⟩ ⟨_ | ⟨⟨n', d', hx', _⟩, y', w'⟩, hQ⟩ hPQ,
  any_goals { contradiction },
  { refl },
  { rw [height, real.log_le_iff_le_exp, max_le_iff, abs_le'] at hP hQ,
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

lemma height_le_constant.fintype (C : ℝ) : fintype {P : E⟮ℚ⟯ // height P ≤ C} :=
begin
  by_cases hC : C < 0,
  { exact @fintype.of_is_empty {P : E⟮ℚ⟯ // height P ≤ C}
      ⟨λ ⟨P, hP⟩, not_le_of_lt hC $ le_trans (height_nonneg P) hP⟩ },
  { exact fintype.of_injective (height_le_constant.function ha₁ ha₃ $ le_of_not_lt hC)
      (height_le_constant.surjective ha₁ ha₃ $ le_of_not_lt hC) }
end

include ha₂ ha₄ ha₆

lemma exists_constant_height_add_le_two_mul_height_add_constant (Q : E⟮ℚ⟯) :
  ∃ C : ℝ, ∀ P : E⟮ℚ⟯, height (P + Q) ≤ 2 * height P + C :=
begin
  cases Q with x' y' w',
  { exact ⟨0, λ P, by simpa only [EllipticCurve.zero_def, add_zero, two_mul]
                      using le_add_of_nonneg_left (height_nonneg P)⟩ },
  { existsi [sorry],
    rintro (_ | ⟨x, y, w⟩),
    { sorry },
    { sorry } }
end

lemma exists_constant_four_mul_height_le_height_two_smul_add_constant :
  ∃ C : ℝ, ∀ P : E⟮ℚ⟯, 4 * height P ≤ height (2 • P) + C :=
begin
  let C₁ : ℝ := (max 12 $ 16 * |A|),
  let C₂ : ℝ := (max 3 $ max (5 * |A|) $ 27 * |B|),
  let C₃ : ℝ := (max (16 * |A| ^ 3 + 108 * B ^ 2) $ max (4 * A ^ 2 * |B|) $
                 max (12 * A ^ 4 + 88 * |A| * B ^ 2) $ 12 * |A| ^ 3 * |B| + 96 * |B| ^ 3),
  let C₄ : ℝ := (max (A ^ 2 * |B|) $ max (5 * A ^ 4 + 32 * |A| * B ^ 2) $
                 max (26 * |A| ^ 3 * |B| + 192 * |B| ^ 3) $ 3 * |A| ^ 5 + 24 * A ^ 2 * B ^ 2),
  existsi [(8 * max C₁ $ max C₂ $ max C₃ C₄).log],
  rintro (_ | ⟨x, y, w⟩),
  { sorry },
  { sorry }
end

end heights

end EllipticCurve

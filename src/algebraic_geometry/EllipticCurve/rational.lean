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

variables {E : EllipticCurve ℚ}
variables (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
variables {A B : ℤ} (hA : E.a₄ = rat.of_int A) (hB : E.a₆ = rat.of_int B)

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------

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

include ha₂ hA hB

lemma padic_val_point {x y w} {P : E⟮ℚ⟯} (hP : P = some x y w) (p : ℕ) [fact $ prime p]
  (hx : padic_val_rat p x ≤ 0) (hy : padic_val_rat p y ≤ 0) :
  ∃ n : ℕ, padic_val_rat p x = -2 * n ∧ padic_val_rat p y = -3 * n :=
begin
  rw [ha₁, ha₂, ha₃, hA, hB] at w,
  simp only [algebra_map_rat_rat, ring_hom.id_apply, zero_mul, add_zero] at w,
  sorry
end

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

end EllipticCurve

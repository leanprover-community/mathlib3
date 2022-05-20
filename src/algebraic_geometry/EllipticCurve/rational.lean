/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import analysis.special_functions.log.basic

import algebraic_geometry.EllipticCurve.torsion

/-!
# The Mordell-Weil theorem for an elliptic curve over the rationals
-/

noncomputable theory
open_locale classical

variables {E : EllipticCurve ℚ}
variables (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
variables {A : ℤ} (hA : rat.of_int A = E.a₄) {B : ℤ} (hB : rat.of_int B = E.a₆)

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------

/-- The logarithmic height of a point on an elliptic curve over the rationals. -/
def height : E⟮ℚ⟯ → ℝ
| 0            := 0
| (some x _ _) := real.log $ max (|x.num|) (|x.denom|)

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

include ha₁ ha₂ ha₃ hA hB

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
  existsi [sorry],
  rintro (_ | ⟨x, y, w⟩),
  { sorry },
  { sorry }
end

def height_le_constant.function {C : ℝ} (hC : 0 ≤ C) : {P : E⟮ℚ⟯ // height P ≤ C}
  → option (fin (2 * ⌊real.exp C⌋₊ + 1) × fin (⌊real.exp C⌋₊ + 1) × fin 2)
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨(x.num + ⌊real.exp C⌋).to_nat, x.denom, if y ≤ 0 then 0 else 1⟩

lemma height_le_constant.surjective {C : ℝ} (hC : 0 ≤ C) :
  function.injective $ @height_le_constant.function E ha₁ ha₂ ha₃ A hA B hB C hC :=
begin
  rintro ⟨_ | ⟨⟨n, d, hx, _⟩, y, w⟩, hP⟩ ⟨_ | ⟨⟨n', d', hx', _⟩, y', w'⟩, hQ⟩ hPQ,
  any_goals { contradiction },
  { refl },
  { rw [height, real.log_le_iff_le_exp, max_le_iff, abs_le', ← int.le_floor, ← int.cast_neg,
        ← int.le_floor, neg_le_iff_add_nonneg', nat.abs_cast,
        ← nat.le_floor_iff $ le_of_lt $ real.exp_pos C, ← nat.lt_add_one_iff] at hP hQ,
    simp only [height_le_constant.function, prod.mk.inj_iff, fin.eq_iff_veq] at hPQ,
    simp only at *,
    rw [fin.coe_val_of_lt, fin.coe_val_of_lt, fin.coe_val_of_lt hP.2,
        fin.coe_val_of_lt hQ.2] at hPQ,
    { have : (↑_ : ℤ) = (_ : ℤ) := congr_arg int.of_nat hPQ.1,
      rw [int.to_nat_of_nonneg hP.1.2, int.to_nat_of_nonneg hQ.1.2, add_right_cancel_iff] at this,
      split,
      exact ⟨this, hPQ.2.1⟩,
      rw [ha₁, ha₃] at w w',
      simp only [algebra_map_rat_rat, ring_hom.id_apply, zero_mul, add_zero, this, hPQ.2.1] at w w',
      rw [← w', sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at w,
      split_ifs at hPQ with hy hy' hy',
      { cases w with hw hw',
        exact hw,
        subst hw',
        have := antisymm' (nonneg_of_neg_nonpos hy) hy',
        subst this,
        refl },
      { exact false.elim (zero_ne_one hPQ.2.2) },
      { exact false.elim (zero_ne_one hPQ.2.2.symm) },
      { cases w with hw hw',
        exact hw,
        subst hw',
        have := antisymm' (nonpos_of_neg_nonneg $ le_of_not_le hy) (le_of_not_le hy'),
        subst this,
        refl } },
    any_goals { rw [nat.lt_add_one_iff, int.to_nat_le, int.coe_nat_mul, ← int.nat_cast_eq_coe_nat,
                    nat.cast_two, nat.cast_floor_eq_int_floor $ le_of_lt $ real.exp_pos C, two_mul,
                    add_le_add_iff_right] },
    { exact hQ.1.1 },
    { exact hP.1.1 },
    any_goals { rw [lt_max_iff, nat.abs_cast, nat.cast_pos] },
    { exact or.inr hx },
    { exact or.inr hx' } }
end

lemma height_le_constant.fintype (C : ℝ) : fintype {P : E⟮ℚ⟯ // height P ≤ C} :=
begin
  by_cases hC : C < 0,
  { exact @fintype.of_is_empty {P : E⟮ℚ⟯ // height P ≤ C}
      ⟨λ ⟨P, hP⟩, not_le_of_lt hC $ le_trans (height_nonneg P) hP⟩ },
  { exact fintype.of_injective (height_le_constant.function ha₁ ha₂ ha₃ hA hB $ le_of_not_lt hC)
      (height_le_constant.surjective ha₁ ha₂ ha₃ hA hB $ le_of_not_lt hC) }
end

end EllipticCurve

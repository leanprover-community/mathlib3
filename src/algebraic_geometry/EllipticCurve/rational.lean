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
variables (A : ℤ) (hA : rat.of_int A = E.a₄) (B : ℤ) (hB : rat.of_int B = E.a₆)

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

def height_le_constant.function (C : ℝ) (hC : 0 ≤ C) : {P : E⟮ℚ⟯ // height P ≤ C}
  → option (fin (2 * ⌊real.exp C⌋₊ + 1) × fin (⌊real.exp C⌋₊ + 1) × fin 2)
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨(x.num + ⌊real.exp C⌋).to_nat, x.denom, if y ≤ 0 then 0 else 1⟩

lemma height_le_constant.surjective (C : ℝ) (hC : 0 ≤ C) :
  function.injective $ @height_le_constant.function E C hC :=
begin
  sorry
end

lemma height_le_constant.fintype (C : ℝ) : fintype {P : E⟮ℚ⟯ // height P ≤ C} :=
begin
  by_cases hC : C < 0,
  { exact @fintype.of_is_empty {P : E⟮ℚ⟯ // height P ≤ C}
      ⟨λ ⟨P, hP⟩, not_le_of_lt hC $ le_trans (height_nonneg P) hP⟩ },
  { exact fintype.of_injective (height_le_constant.function C $ le_of_not_lt hC)
      (height_le_constant.surjective C $ le_of_not_lt hC) }
end

end EllipticCurve

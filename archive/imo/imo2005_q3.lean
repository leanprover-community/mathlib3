/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.real.basic

/-!
# IMO 2005 Q3
Let `x`, `y` and `z` be positive real numbers such that `xyz ≥ 1`. Prove that:
`(x^5 - x^2)/(x^5 + y^2 + z^2) + (y^5 - y^2)/(y^5 + z^2 + x^2) + (z^5 - z^2)/(z^5 + x^2 + y^2) ≥ 0`

# Solution
The solution by Iurie Boreico from Moldova is presented, which won a special prize during the exam.
The key insight is that `(x^5-x^2)/(x^5+y^2+z^2) ≥ (x^2-y*z)/(x^2+y^2+z^2)`, which is proven by
factoring `(x^5-x^2)/(x^5+y^2+z^2) - (x^5-x^2)/(x^3*(x^2+y^2+z^2))` into a non-negative expression
and then making use of `xyz ≥ 1` to show `(x^5-x^2)/(x^3*(x^2+y^2+z^2)) ≥ (x^2-y*z)/(x^2+y^2+z^2)`.
-/

lemma key_insight (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x*y*z ≥ 1) :
  (x^5-x^2)/(x^5+y^2+z^2) ≥ (x^2-y*z)/(x^2+y^2+z^2) :=
begin
  have h₁ : x^5+y^2+z^2 > 0, linarith [pow_pos hx 5, pow_pos hy 2, pow_pos hz 2],
  have h₂ : x^3 > 0, exact pow_pos hx 3,
  have h₃ : x^2+y^2+z^2 > 0, linarith [pow_pos hx 2, pow_pos hy 2, pow_pos hz 2],
  have h₄ : x^3*(x^2+y^2+z^2) > 0, exact mul_pos h₂ h₃,

  have key : (x^5-x^2)/(x^5+y^2+z^2) - (x^5-x^2)/(x^3*(x^2+y^2+z^2))
           = ((x^3 - 1)^2*x^2*(y^2 + z^2))/((x^5+y^2+z^2)*(x^3*(x^2+y^2+z^2))),
  calc  (x^5-x^2)/(x^5+y^2+z^2) - (x^5-x^2)/(x^3*(x^2+y^2+z^2))
      = ((x^5-x^2)*(x^3*(x^2+y^2+z^2))-(x^5+y^2+z^2)*(x^5-x^2))/((x^5+y^2+z^2)*(x^3*(x^2+y^2+z^2))):
        by exact div_sub_div _ _ (ne_of_gt h₁) (ne_of_gt h₄)    -- a/b - c/d = (a*d-b*c)/(b*d)
  ... = ((x^3 - 1)^2*x^2*(y^2 + z^2))/((x^5+y^2+z^2)*(x^3*(x^2+y^2+z^2))) :
        by ring,

  have h₅ : ((x^3 - 1)^2*x^2*(y^2 + z^2))/((x^5+y^2+z^2)*(x^3*(x^2+y^2+z^2))) ≥ 0,
  { refine div_nonneg _ _,
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) _,
    exact add_nonneg (sq_nonneg _) (sq_nonneg _),
    exact le_of_lt (mul_pos h₁ h₄) },

  calc  (x^5-x^2)/(x^5+y^2+z^2)
      ≥ (x^5-x^2)/(x^3*(x^2+y^2+z^2)) : by linarith [key, h₅]
  ... ≥ (x^5-x^2*(x*y*z))/(x^3*(x^2+y^2+z^2)) :
        by { refine (div_le_div_right h₄).mpr _, simp,
             exact (le_mul_iff_one_le_right (pow_pos hx 2)).mpr h }
  ... = (x^2-y*z)/(x^2+y^2+z^2) :
        by { field_simp [ne_of_gt h₂, ne_of_gt h₃], ring },
end

theorem imo2005_q3 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x*y*z ≥ 1) :
  (x^5-x^2)/(x^5+y^2+z^2) + (y^5-y^2)/(y^5+z^2+x^2) + (z^5-z^2)/(z^5+x^2+y^2) ≥ 0 :=
begin
  calc  (x^5-x^2)/(x^5+y^2+z^2) + (y^5-y^2)/(y^5+z^2+x^2) + (z^5-z^2)/(z^5+x^2+y^2)
      ≥ (x^2-y*z)/(x^2+y^2+z^2) + (y^2-z*x)/(y^2+z^2+x^2) + (z^2-x*y)/(z^2+x^2+y^2) :
        by { linarith [key_insight x y z hx hy hz h,
                       key_insight y z x hy hz hx (by linarith [h]),
                       key_insight z x y hz hx hy (by linarith [h])] }
  ... = (x^2 + y^2 + z^2 - y*z - z*x - x*y) / (x^2+y^2+z^2) :
        by { have h₁ : y^2+z^2+x^2 = x^2+y^2+z^2, linarith,
             have h₂ : z^2+x^2+y^2 = x^2+y^2+z^2, linarith,
             rw [h₁, h₂], ring }
  ... = 1/2*( (x-y)^2 + (y-z)^2 + (z-x)^2 ) / (x^2+y^2+z^2) : by ring
  ... ≥ 0 :
        by { exact div_nonneg
                (by linarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)])
                (by linarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]) },
end

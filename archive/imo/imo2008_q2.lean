/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales.
-/
import data.real.basic

/-!
# IMO 2008 Q2
(a) Prove that
          ```x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1```
    for all real numbers x, y, z, each different from 1, and satisfying xyz = 1.

(b) Prove that equality holds above for infinitely many triples of rational numbers x, y, z, each
different from 1, and satisfying xyz = 1.

# Solution
(a) Since xyz = 1, we can apply the substitution x = a/b, y = b/c, z = c/a.
Then we define m = c-b, n = b-a and rewrite the inequaility as LHS - 1 ≥ 0
using c, m and n. We factor LHS - 1 as a square, which finishes the proof.
-/

lemma subst_abc (x y z : ℝ) (h : x*y*z = 1) :
  ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a/b ∧ y = b/c ∧ z = c /a :=
begin
  use x, use 1, use 1/y,
  have h₁ : x ≠ 0               := by { intro p, rw p at h, simp at h, exact h },
  have h₂ : (1 : ℝ)  ≠ (0 : ℝ)  := by { exact one_ne_zero },
  have hy_ne_zero : y ≠ 0       := by { intro p, rw p at h, simp at h, exact h },
  have h₃ : 1/y ≠ 0             := by { exact one_div_ne_zero hy_ne_zero },
  have h₄ : x = x / 1           := by { exact (div_one x).symm },
  have h₅ : y = 1 / (1 / y)     := by { exact (one_div_one_div y).symm },
  have h₆ : z = 1 / y / x       := by { field_simp, linarith [h] },
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩,
end

theorem imo2008_q2_a (x y z : ℝ) (h : x*y*z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
  x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1 :=
begin
  rcases (subst_abc _ _ _ h) with ⟨a, b, c, ha, hb, hc, hx₂, hy₂, hz₂⟩,

  let m := c-b,
  let n := b-a,

  have hm_abc : m = c - b         := by exact rfl,
  have hn_abc : n = b - a         := by exact rfl,
  have ha_cmn : a = c - m - n     := by linarith,
  have hb_cmn : b = c - m         := by linarith,
  have hab_mn : (a-b)^2 = n^2     := by { rw [ha_cmn, hb_cmn], ring },
  have hbc_mn : (b-c)^2 = m^2     := by { rw hb_cmn, ring },
  have hca_mn : (c-a)^2 = (m+n)^2 := by { rw ha_cmn, ring },

  have hm_ne_zero : m ≠ 0 :=
  by { rw hm_abc, rw hy₂ at hy, intro p, apply hy, field_simp, linarith },

  have hn_ne_zero : n ≠ 0 :=
  by { rw hn_abc, rw hx₂ at hx, intro p, apply hx, field_simp, linarith },

  have hmn_ne_zero : m + n ≠ 0 :=
  by { rw hm_abc, rw hn_abc, rw hz₂ at hz, intro p, apply hz, field_simp, linarith },

  have key : x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 - 1 ≥ 0,

  calc  x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 - 1
      = (a/b)^2 / (a/b-1)^2 + (b/c)^2 / (b/c-1)^2 + (c/a)^2 / (c/a-1)^2 - 1 :
        by rw [hx₂, hy₂, hz₂]
  ... = a^2/(a-b)^2 + b^2/(b-c)^2 + c^2/(c-a)^2 - 1 :
        by field_simp [div_sub_one hb, div_sub_one hc, div_sub_one ha]
  ... = (c-m-n)^2/n^2 + (c-m)^2/m^2 + c^2/(m+n)^2 - 1 :
        by { rw [hab_mn, hbc_mn, hca_mn, ha_cmn, hb_cmn] }
  ... = ( (c*(m^2+n^2+m*n) - m*(m+n)^2) / (m*n*(m+n)) )^2 :
        by { ring_nf, field_simp, ring }
  ... ≥ 0 :
        by { exact pow_two_nonneg _ },

  linarith [key],
end

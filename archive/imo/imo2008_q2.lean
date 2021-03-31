/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.real.basic
import data.set.basic
import data.set.finite

/-!
# IMO 2008 Q2
(a) Prove that
          ```x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1```
for all real numbers x, y, z, each different from 1, and satisfying xyz = 1.

(b) Prove that equality holds above for infinitely many triples of rational numbers x, y, z, each
different from 1, and satisfying xyz = 1.

# Solution
(a) Since xyz = 1, we can apply the substitution x = a/b, y = b/c, z = c/a.
Then we define m = c-b, n = b-a and rewrite the inequality as LHS - 1 ≥ 0
using c, m and n. We factor LHS - 1 as a square, which finishes the proof.

(b) We present a set W of rational triples. We prove that W is a subset of the
set of rational solutions to the equation, and that W is infinite.
-/

lemma subst_abc (x y z : ℝ) (h : x*y*z = 1) :
  ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a/b ∧ y = b/c ∧ z = c /a :=
begin
  use x, use 1, use 1/y,
  have h₁ : x ≠ 0,              { intro p, rw p at h, simp at h, exact h },
  have h₂ : (1 : ℝ) ≠ (0 : ℝ),  exact one_ne_zero,
  have hy_ne_zero : y ≠ 0,      { intro p, rw p at h, simp at h, exact h },
  have h₃ : 1/y ≠ 0,            exact one_div_ne_zero hy_ne_zero,
  have h₄ : x = x / 1,          exact (div_one x).symm,
  have h₅ : y = 1 / (1 / y),    exact (one_div_one_div y).symm,
  have h₆ : z = 1 / y / x,      { field_simp, linarith [h] },
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩,
end

theorem imo2008_q2a (x y z : ℝ) (h : x*y*z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
  x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1 :=
begin
  rcases (subst_abc _ _ _ h) with ⟨a, b, c, ha, hb, hc, hx₂, hy₂, hz₂⟩,

  let m := c-b,
  let n := b-a,

  have hm_abc : m = c - b,          exact rfl,
  have hn_abc : n = b - a,          exact rfl,
  have ha_cmn : a = c - m - n,      linarith,
  have hb_cmn : b = c - m,          linarith,
  have hab_mn : (a-b)^2 = n^2,      { rw [ha_cmn, hb_cmn], ring },
  have hbc_mn : (b-c)^2 = m^2,      rw hb_cmn, ring,
  have hca_mn : (c-a)^2 = (m+n)^2,  rw ha_cmn, ring,

  have hm_ne_zero : m ≠ 0,
  { rw hm_abc, rw hy₂ at hy, intro p, apply hy, field_simp, linarith },

  have hn_ne_zero : n ≠ 0,
  { rw hn_abc, rw hx₂ at hx, intro p, apply hx, field_simp, linarith },

  have hmn_ne_zero : m + n ≠ 0,
  { rw hm_abc, rw hn_abc, rw hz₂ at hz, intro p, apply hz, field_simp, linarith },

  have key : x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 - 1 ≥ 0,

  calc  x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 - 1
      = (a/b)^2 / (a/b-1)^2 + (b/c)^2 / (b/c-1)^2 + (c/a)^2 / (c/a-1)^2 - 1 :
        by rw [hx₂, hy₂, hz₂]
  ... = a^2/(a-b)^2 + b^2/(b-c)^2 + c^2/(c-a)^2 - 1 :
        by field_simp [div_sub_one hb, div_sub_one hc, div_sub_one ha]
  ... = (c-m-n)^2/n^2 + (c-m)^2/m^2 + c^2/(m+n)^2 - 1 :
        by rw [hab_mn, hbc_mn, hca_mn, ha_cmn, hb_cmn]
  ... = ( (c*(m^2+n^2+m*n) - m*(m+n)^2) / (m*n*(m+n)) )^2 :
        by { ring_nf, field_simp, ring }
  ... ≥ 0 :
        by exact pow_two_nonneg _ ,

  linarith [key],
end

def rational_solutions := { s : ℚ×ℚ×ℚ | ∃ (x y z : ℚ), s = (x, y, z) ∧
  x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x*y*z = 1 ∧ x^2/(x-1)^2 + y^2/(y-1)^2 + z^2/(z-1)^2 = 1 }

theorem imo2008_q2b : set.infinite rational_solutions :=
begin
  let W := { s : ℚ×ℚ×ℚ | ∃ (x y z : ℚ), s = (x, y, z) ∧
    ∃ t : ℚ, t > 0 ∧ x = -(t+1)/t^2 ∧ y = t/(t+1)^2 ∧ z = -t*(t+1)},

  have hW_sub_S : W ⊆ rational_solutions,
  { intros s hs_in_W,
    rw rational_solutions,
    simp at hs_in_W ⊢,
    rcases hs_in_W with ⟨x, y, z, hs_xyz, ht⟩,
    rcases ht with ⟨t, ht_gt_zero, hx_t, hy_t, hz_t⟩,
    use x, use y, use z,

    have ht_ne_zero : t ≠ 0, exact ne_of_gt ht_gt_zero,
    have ht1_ne_zero : t+1 ≠ 0, linarith[ht_gt_zero],

    have key_gt_zero : t^2 + t + 1 > 0, linarith[pow_pos ht_gt_zero 2, ht_gt_zero],
    have key_ne_zero : t^2 + t + 1 ≠ 0, exact ne_of_gt key_gt_zero,

    have h₂ : x ≠ 1, { rw hx_t, field_simp, linarith[key_gt_zero] },
    have h₃ : y ≠ 1, { rw hy_t, field_simp, linarith[key_gt_zero] },
    have h₄ : z ≠ 1, { rw hz_t, linarith[key_gt_zero] },

    have h₅ : x*y*z = 1, { rw [hx_t, hy_t, hz_t], field_simp, ring },

    have h₆ : x^2/(x-1)^2 + y^2/(y-1)^2 + z^2/(z-1)^2 = 1,
    { have hx1 : (x - 1)^2 = (t^2 + t + 1)^2/t^4,
      { field_simp, rw hx_t, field_simp, ring },
      have hy1 : (y - 1)^2 = (t^2 + t + 1)^2/(t+1)^4,
      { field_simp, rw hy_t, field_simp, ring },
      have hz1 : (z - 1)^2 = (t^2 + t + 1)^2,
      { rw hz_t, ring },
      calc  x^2/(x-1)^2 + y^2/(y-1)^2 + z^2/(z-1)^2
          = (x^2*t^4 + y^2*(t+1)^4 + z^2)/(t^2 + t + 1)^2 :
            by { rw [hx1, hy1, hz1], field_simp }
      ... = 1 :
            by { rw [hx_t, hy_t, hz_t], field_simp, ring } },

    exact ⟨hs_xyz, h₂, h₃, h₄, h₅, h₆⟩,
  },

  have hW_inf : set.infinite W,
  { let g : ℚ×ℚ×ℚ → ℚ := (λs, -s.2.2),
    let Z := g '' W,

    have hZ_not_bdd : ¬bdd_above Z,
    { rw not_bdd_above_iff,
      intro q,
      let t : ℚ := max (q+1) 1,
      use t*(t+1),
      let x : ℚ := (-1 + -t)/t^2,
      let y : ℚ := t/(t+1)^2,
      let z : ℚ := -t*(t+1),
      have hz_def : z = -t*(t+1), exact rfl,

      split,
      { simp, use x, use y, use z, split,
        { use x, use y, use z, split,
          { split, refl, split, refl, refl },
          { use t, split,
            { simp, right, exact zero_lt_one },
            { split, refl, split, refl, linarith[hz_def] } } },
        { have hg_eval : g(x, y, z) = -z, exact rfl,
          rw hg_eval, linarith[hz_def] } },
      { calc q < q + 1    : by { linarith }
           ... ≤ t        : by { exact le_max_left (q + 1) 1 }
           ... ≤ t+t^2    : by { linarith [pow_two_nonneg t] }
           ... = t*(t+1)  : by { ring } },
    },

    have hZ_inf : set.infinite Z,
    { intro h, apply hZ_not_bdd, exact set.finite.bdd_above h },

    exact set.infinite_of_infinite_image g hZ_inf,
  },

  exact set.infinite_mono hW_sub_S hW_inf,
end

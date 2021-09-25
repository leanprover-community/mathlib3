/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials
import algebra.archimedean

@[simp]
lemma real.norm_nat_cast : ∀ (n : ℕ), ∥(n : ℝ)∥ = (n : ℝ)
| 0 := norm_zero.trans (nat.cast_zero).symm
| (n + 1) := abs_eq_self.2 (nat.cast_nonneg (n + 1))

-- TODO: Not sure the best name for this lemma
lemma exists_nat_norm_gt (x : ℝ) : ∃ (n : ℕ), x < ∥(n : ℝ)∥ :=
let ⟨n, hn⟩ := exists_nat_gt x in
  ⟨n, lt_of_lt_of_le hn (le_of_eq (real.norm_nat_cast n).symm)⟩

@[simp]
lemma norm_nat_cast_le_iff (n m : ℕ) :
  ∥(n : ℝ)∥ ≤ ∥(m : ℝ)∥ ↔ n ≤ m :=
by simp only [real.norm_nat_cast, nat.cast_le]

namespace asymptotics

variables {𝕜 : Type*} [normed_field 𝕜]

def negligible (f : ℕ → 𝕜) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

variables {f g : ℕ → 𝕜}

lemma negligible_of_is_O_negligible (h : is_O f g filter.at_top)
  (hg : negligible g) : negligible f :=
λ c, h.trans $ hg c

@[simp]
lemma negligible_zero : negligible (function.const ℕ (0 : 𝕜)) :=
λ c, is_O_zero _ _

@[simp]
lemma negligable_const_iff {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  (x : 𝕜) : negligible (function.const ℕ x) ↔ x = 0 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ negligible_zero⟩,
  refine (not_not.1 (λ hx, _)),
  specialize h (-1),

  rw is_O_iff at h,
  obtain ⟨c, hc⟩ := h,
  simp only [filter.eventually_at_top, function.const_apply, gpow_one, ge_iff_le,
    fpow_neg, normed_field.norm_inv] at hc,
  -- by_contradiction hx,
  obtain ⟨a, ha⟩ := hc,
  obtain ⟨n, hn⟩ := exists_nat_norm_gt (c * ∥x∥⁻¹),
  specialize ha (max a (max n 1)) (le_max_left a (max n 1)),
  rw mul_inv_lt_iff (norm_pos_iff.2 hx) at hn,
  rw [← not_lt, (mul_inv_lt_iff (norm_pos_iff.2 _))] at ha,
  refine ha (lt_of_lt_of_le hn _),
  {
    rw mul_comm (∥x∥),
    refine mul_le_mul_of_nonneg_right _ _,
    refine (norm_nat_cast_le_iff _ _).2 _,
    refine le_trans (le_max_right a n) _,
    refine max_le_max le_rfl (le_max_left _ _),
    refine norm_nonneg x,
  },
  {
    suffices : 0 < max a (max n 1),
    {
      refine ne.symm (ne_of_lt _),
      refine nat.cast_pos.2 this,
    },
    refine lt_max_of_lt_right _,
    refine lt_max_of_lt_right _,
    refine zero_lt_one,
  }
end

lemma negligible_add (hf : negligible f) (hg : negligible g) :
  negligible (f + g) :=
λ c, (hf c).add $ hg c

end asymptotics

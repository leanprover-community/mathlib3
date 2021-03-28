import analysis.complex.basic
import data.complex.exponential
import data.real.sqrt
import analysis.normed_space.linear_isometry

open complex

local notation `|` x `|` := complex.abs x

lemma conj_sub (z z': ℂ) : conj (z - z') = conj z - conj z' := conj.map_sub z z'

lemma conj_one : conj 1 = 1 := by rw conj.map_one

lemma add_self_eq (a : ℝ) : a + a = a * 2 := by ring

-- http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf
lemma linear_isometry_complex_aux (z : ℂ) (f : ℂ →ₗᵢ[ℝ] ℂ) :
  f 0 = 0 → f 1 = 1 → ((f z = z) ∨ (f z = conj z)) :=
begin
  intros h₀ h₁,
  have hf0 : |f z - f 0| = |z - 0| := by exact linear_isometry.dist_map f z 0,
  rw h₀ at hf0,
  iterate 2 { rw sub_zero at hf0 },
  have hf1 : |f z - f 1| = |z - 1| := by exact linear_isometry.dist_map f z 1,
  rw h₁ at hf1,
  have h₂ : conj (f z - 1) * (f z - 1) = conj (z - 1) * (z - 1) :=
    begin
      iterate 2 { rw ← norm_sq_eq_conj_mul_self },
      iterate 2 { rw ← mul_self_abs },
      rw hf1,
    end,
  iterate 2 { rw conj_sub at h₂ },
  iterate 2 { rw sub_mul at h₂ },
  iterate 4 { rw mul_sub at h₂ },
  rw conj_one at h₂,
  rw mul_one at h₂,
  iterate 2 { rw one_mul at h₂ },
  rw mul_one at h₂,
  rw one_mul at h₂,
  iterate 2 { rw ← norm_sq_eq_conj_mul_self at h₂ },
  iterate 2 { rw ← mul_self_abs at h₂ },
  iterate 2 { rw ← sub_add at h₂ },
  rw hf0 at h₂,
  have h₃ : z + conj z = f z + conj (f z) := by {
    iterate 2 { rw ← sub_add_eq_sub_sub at h₂ },
    iterate 2 { rw sub_add at h₂ },
    rw ← neg_add_eq_sub at h₂,
    rw ← neg_add_eq_sub (conj z + z - 1) at h₂,
    rw add_right_cancel_iff at h₂,
    iterate 2 { rw add_sub_assoc at h₂ },
    iterate 2 { rw neg_add' at h₂ },
    iterate 2 { rw ← sub_add at h₂ },
    rw add_right_cancel_iff at h₂,
    iterate 2 { rw ← neg_add' at h₂ },
    rw add_comm at h₂,
    rw add_comm (conj z) z at h₂,
    rw ← @add_left_cancel_iff _ _ (z + conj z) at h₂,
    rw add_neg_self at h₂,
    rw ← @add_right_cancel_iff _ _ (f z + conj (f z)) at h₂,
    rw zero_add at h₂,
    rw add_assoc at h₂,
    rw neg_add_self at h₂,
    rw add_zero at h₂,
    rw h₂,
  },
  have hf_re : (f z).re = z.re := by {
    rw ext_iff at h₃,
    iterate 2 { rw add_re at h₃ },
    iterate 2 { rw add_im at h₃ },
    iterate 2 { rw conj_re at h₃ },
    iterate 2 { rw conj_im at h₃ },
    iterate 2 { rw add_neg_self at h₃ },
    iterate 2 { rw add_self_eq at h₃ },
    cases h₃,
    rw eq_comm at h₃_left,
    linarith [h₃_left],
  },
  have hf_im : (f z).im = z.im ∨ (f z).im = -z.im := by {
    iterate 2 { rw complex.abs at hf0 },
    rw real.sqrt_inj at hf0,
    swap,
    exact norm_sq_nonneg (f z),
    swap,
    exact norm_sq_nonneg z,
    rw norm_sq_apply (f z) at hf0,
    rw norm_sq_apply z at hf0,
    rw hf_re at hf0,
    rw add_left_cancel_iff at hf0,
    rw mul_self_eq_mul_self_iff at hf0,
    exact hf0,
  },
  iterate 2 { rw ext_iff },
  rw conj_re,
  rw conj_im,
  rw ← and_or_distrib_left,
  exact ⟨hf_re, hf_im⟩,
end

lemma linear_isometry_complex (z : ℂ) (f : ℂ →ₗᵢ[ℝ] ℂ) :
  ∃ a : ℂ, |a| = 1 ∧ ((f z = a * z) ∨ (f z = a * conj z)) :=
begin
  let a := f 1,
  let g : ℂ →ₗᵢ[ℝ] ℂ :=
    { to_fun := λ z, a⁻¹ * f z,
      map_add' := by {
        intros x y,
        rw linear_isometry.map_add,
        rw mul_add,
      },
      map_smul' := by {
        intros m x,
        rw linear_isometry.map_smul,
        rw algebra.mul_smul_comm,
      },
      norm_map' := by {
        intros x,
        simp,
        change ∥f 1∥⁻¹ * ∥f x∥ = ∥x∥,
        iterate 2 { rw linear_isometry.norm_map },
        simp,
      },
    },
  use a,
  split,
    {
      change ∥a∥ = 1,
      simp only [a],
      rw linear_isometry.norm_map,
      simp
    },
    {
      have hg0 : g 0 = 0 := g.map_zero,
      have hg1 : g 1 = 1 := by {
        change a⁻¹ * a = 1,
        rw inv_mul_cancel,
        rw ← norm_sq_pos,
        rw norm_sq_eq_abs,
        change 0 < ∥a∥ ^ 2,
        rw linear_isometry.norm_map,
        simp,
        apply zero_lt_one,
      },
      have h : g z = z ∨ g z = conj z := linear_isometry_complex_aux z g hg0 hg1,
      have ha : a ≠ 0 := by {
        rw ← norm_sq_pos,
        rw norm_sq_eq_abs,
        change 0 < ∥a∥ ^ 2,
        rw linear_isometry.norm_map,
        simp,
        apply zero_lt_one,
      },
      have ha_inv : a⁻¹ ≠ 0 := by {
        exact inv_ne_zero ha,
      },
      conv { congr, rw ← mul_right_inj' ha_inv, rw ← mul_assoc, rw inv_mul_cancel ha, rw one_mul, change g z = z },
      conv { congr, skip, rw ← mul_right_inj' ha_inv, rw ← mul_assoc, rw inv_mul_cancel ha, rw one_mul, change g z = conj z },
      exact h,
    }
end

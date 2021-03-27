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
lemma linear_isometry_complex' (z : ℂ) (h : ℂ →ₗᵢ[ℝ] ℂ) :
  h 0 = 0 → h 1 = 1 → ((h z = z) ∨ (h z = conj z)) :=
begin
  intros h0 h1,
  have H0 : |h z - h 0| = |z - 0| := by exact linear_isometry.dist_map h z 0,
  rw h0 at H0,
  iterate 2 { rw sub_zero at H0 },
  have H1 : |h z - h 1| = |z - 1| := by exact linear_isometry.dist_map h z 1,
  rw h1 at H1,
  have H12 : conj (h z - 1) * (h z - 1) = conj (z - 1) * (z - 1) :=
    begin
      iterate 2 { rw ← norm_sq_eq_conj_mul_self },
      iterate 2 { rw ← mul_self_abs },
      rw H1,
    end,
  iterate 2 { rw conj_sub at H12 },
  iterate 2 { rw sub_mul at H12 },
  iterate 4 { rw mul_sub at H12 },
  rw conj_one at H12,
  rw mul_one at H12,
  iterate 2 { rw one_mul at H12 },
  rw mul_one at H12,
  rw one_mul at H12,
  iterate 2 { rw ← norm_sq_eq_conj_mul_self at H12 },
  iterate 2 { rw ← mul_self_abs at H12 },
  iterate 2 { rw ← sub_add at H12 },
  rw H0 at H12,
  have H : z + conj z = h z + conj (h z) := by {
    iterate 2 { rw ← sub_add_eq_sub_sub at H12 },
    iterate 2 { rw sub_add at H12 },
    rw ← neg_add_eq_sub at H12,
    rw ← neg_add_eq_sub (conj z + z - 1) at H12,
    rw add_right_cancel_iff at H12,
    iterate 2 { rw add_sub_assoc at H12 },
    iterate 2 { rw neg_add' at H12 },
    iterate 2 { rw ← sub_add at H12 },
    rw add_right_cancel_iff at H12,
    iterate 2 { rw ← neg_add' at H12 },
    rw add_comm at H12,
    rw add_comm (conj z) z at H12,
    rw ← @add_left_cancel_iff _ _ (z + conj z) at H12,
    rw add_neg_self at H12,
    rw ← @add_right_cancel_iff _ _ (h z + conj (h z)) at H12,
    rw zero_add at H12,
    rw add_assoc at H12,
    rw neg_add_self at H12,
    rw add_zero at H12,
    rw H12,
  },
  have Hre : (h z).re = z.re := by {
    rw ext_iff at H,
    iterate 2 { rw add_re at H },
    iterate 2 { rw add_im at H },
    iterate 2 { rw conj_re at H },
    iterate 2 { rw conj_im at H },
    iterate 2 { rw add_neg_self at H },
    iterate 2 { rw add_self_eq at H },
    cases H,
    rw eq_comm at H_left,
    linarith [H_left],
  },
  have Him : (h z).im = z.im ∨ (h z).im = -z.im := by {
    iterate 2 { rw complex.abs at H0 },
    rw real.sqrt_inj at H0,
    swap,
    exact norm_sq_nonneg (h z),
    swap,
    exact norm_sq_nonneg z,
    rw norm_sq_apply (h z) at H0,
    rw norm_sq_apply z at H0,
    rw Hre at H0,
    rw add_left_cancel_iff at H0,
    rw mul_self_eq_mul_self_iff at H0,
    exact H0,
  },
  iterate 2 { rw ext_iff },
  rw conj_re,
  rw conj_im,
  rw ← and_or_distrib_left,
  exact ⟨Hre, Him⟩,
end

lemma linear_isometry_complex (z : ℂ) (f : ℂ →ₗᵢ[ℝ] ℂ) :
  ∃ a : ℂ, |a| = 1 ∧ ((f z = a * z) ∨ (f z = a * conj z)) :=
begin
  let a := f 1,
  let h : ℂ →ₗᵢ[ℝ] ℂ :=
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
      have H0 : h 0 = 0 := h.map_zero,
      have H1 : h 1 = 1 := by {
        change a⁻¹ * a = 1,
        rw inv_mul_cancel,
        rw ← norm_sq_pos,
        rw norm_sq_eq_abs,
        change 0 < ∥a∥ ^ 2,
        rw linear_isometry.norm_map,
        simp,
        apply zero_lt_one,
      },
      have H2 : h z = z ∨ h z = conj z := linear_isometry_complex' z h H0 H1,
      have H4 : a ≠ 0 := by {
        rw ← norm_sq_pos,
        rw norm_sq_eq_abs,
        change 0 < ∥a∥ ^ 2,
        rw linear_isometry.norm_map,
        simp,
        apply zero_lt_one,
      },
      have H3 : a⁻¹ ≠ 0 := by {
        exact inv_ne_zero H4,
      },
      conv { congr, rw ← mul_right_inj' H3, rw ← mul_assoc, rw inv_mul_cancel H4, rw one_mul, change h z = z },
      conv { congr, skip, rw ← mul_right_inj' H3, rw ← mul_assoc, rw inv_mul_cancel H4, rw one_mul, change h z = conj z },
      exact H2,
    }
end

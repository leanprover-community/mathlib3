/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.inner_product_space.calculus
import analysis.inner_product_space.dual
import analysis.inner_product_space.adjoint
import analysis.calculus.lagrange_multipliers
import analysis.normed_space.compact_map
import linear_algebra.eigenspace
import algebra.star.self_adjoint
import analysis.normed_space.pointwise

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

The main results of this file are `is_self_adjoint.has_eigenvector_of_is_max_on` and
`is_self_adjoint.has_eigenvector_of_is_min_on`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `supr`/`infi` of `λ x, ⟪T x, x⟫ / ∥x∥ ^ 2` is the corresponding
eigenvalue.

The corollaries `is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` and
`is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` state that if `E` is finite-dimensional
and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the `supr`/`infi` of
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ∥x∥ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ∥x∥ ^ 2` (not necessarily both).

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
open_locale nnreal complex_conjugate topological_space filter

open module.End metric

namespace continuous_linear_map
variables (T : E →L[𝕜] E)
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2
local notation `rayleigh_quotient_sphere` :=
λ x : sphere (0:E) 1, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2

lemma rayleigh_smul (x : E) {c : 𝕜} (hc : c ≠ 0) :
  rayleigh_quotient (c • x) = rayleigh_quotient x :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have : ∥c∥ ≠ 0 := by simp [hc],
  have : ∥x∥ ≠ 0 := by simp [hx],
  field_simp [norm_smul, T.re_apply_inner_self_smul],
  ring
end

lemma image_rayleigh_eq_image_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  rayleigh_quotient '' {0}ᶜ = rayleigh_quotient '' (sphere 0 r) :=
begin
  ext a,
  split,
  { rintros ⟨x, (hx : x ≠ 0), hxT⟩,
    have : ∥x∥ ≠ 0 := by simp [hx],
    let c : 𝕜 := ↑∥x∥⁻¹ * r,
    have : c ≠ 0 := by simp [c, hx, hr.ne'],
    refine ⟨c • x, _, _⟩,
    { field_simp [norm_smul, is_R_or_C.norm_eq_abs, abs_of_nonneg hr.le] },
    { rw T.rayleigh_smul x this,
      exact hxT } },
  { rintros ⟨x, hx, hxT⟩,
    exact ⟨x, ne_zero_of_mem_sphere hr.ne' ⟨x, hx⟩, hxT⟩ },
end

lemma supr_rayleigh_eq_supr_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨆ x : {x : E // x ≠ 0}, rayleigh_quotient x) = ⨆ x : sphere (0:E) r, rayleigh_quotient x :=
show (⨆ x : ({0} : set E)ᶜ, rayleigh_quotient x) = _,
by simp only [@csupr_set _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

lemma infi_rayleigh_eq_infi_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨅ x : {x : E // x ≠ 0}, rayleigh_quotient x) = ⨅ x : sphere (0:E) r, rayleigh_quotient x :=
show (⨅ x : ({0} : set E)ᶜ, rayleigh_quotient x) = _,
by simp only [@cinfi_set _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

lemma rayleigh_le_norm (x : E) : rayleigh_quotient x ≤ ∥T∥ :=
begin
  by_cases hx : x = 0,
  { simp only [hx, div_zero, nat.one_ne_zero, norm_zero, ne.def, norm_nonneg, not_false_iff,
               bit0_eq_zero, zero_pow'] },
  have h : T.re_apply_inner_self x ≤ ∥T x∥ * ∥x∥ := re_inner_le_norm (T x) x,
  refine (div_le_iff _).mpr _,
  refine pow_two_pos_of_ne_zero _ (ne_of_gt (norm_pos_iff.mpr hx)),
  calc _ ≤ ∥T x∥ * ∥x∥       : h
      ... ≤ ∥T∥ * ∥x∥ * ∥x∥  : mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)
      ... = ∥T∥ * ∥x∥ ^ 2    : by rw [mul_assoc, pow_two],
end

lemma neg_rayleigh_le_norm (x : E) : -rayleigh_quotient x ≤ ∥T∥ :=
begin
  have h := rayleigh_le_norm (-T) x,
  rw [norm_neg] at h,
  simp only [re_apply_inner_self, neg_apply, inner_neg_left, add_monoid_hom.map_neg] at h,
  simp only [re_apply_inner_self, ←neg_div, h],
end

lemma supr_rayleigh_le_norm : (⨆ x, rayleigh_quotient x) ≤ ∥T∥ :=
csupr_le (λ x, rayleigh_le_norm T x)

lemma supr_neg_rayleigh_le_norm : (⨆ x, -rayleigh_quotient x) ≤ ∥T∥ :=
csupr_le (λ x, neg_rayleigh_le_norm T x)

lemma rayleigh_sphere_eq (x : sphere (0:E) 1) : rayleigh_quotient x = is_R_or_C.re ⟪T x, x⟫ :=
by { simp_rw [norm_eq_of_mem_sphere x, one_pow 2, div_one _], refl }

-- moveme
include 𝕜
lemma sphere_nonempty [nontrivial E] {r : ℝ} (hr : 0 ≤ r) : nonempty (sphere (0:E) r) :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  exact (sphere (0:E) r).nonempty_coe_sort.mpr (normed_space.sphere_nonempty.mpr hr),
end
omit 𝕜

lemma supr_rayleigh_sphere_le_norm [nontrivial E] {r : ℝ} (hr : 0 ≤ r) :
  (⨆ x : sphere (0:E) r, rayleigh_quotient x) ≤ ∥T∥ :=
begin
  haveI : nonempty (sphere (0:E) r) := sphere_nonempty hr,
  exact csupr_le (λ x, rayleigh_le_norm T x),
end

lemma supr_neg_rayleigh_sphere_le_norm [nontrivial E] {r : ℝ} (hr : 0 ≤ r) :
  (⨆ x : sphere (0:E) r, -rayleigh_quotient x) ≤ ∥T∥ :=
begin
  haveI : nonempty (sphere (0:E) r) := sphere_nonempty hr,
  exact csupr_le (λ x, neg_rayleigh_le_norm T x),
end


lemma rayleigh_bdd_above : bdd_above (set.range rayleigh_quotient) :=
begin
  refine set.nonempty_def.mpr ⟨∥T∥, mem_upper_bounds.mpr (λ x hx, _)⟩,
  rw [set.mem_range] at hx,
  rcases hx with ⟨y, hy⟩,
  rw [←hy],
  exact rayleigh_le_norm T y
end

lemma rayleigh_bdd_above_sphere : bdd_above (set.range rayleigh_quotient_sphere) :=
begin
  refine set.nonempty_def.mpr ⟨∥T∥, mem_upper_bounds.mpr (λ x hx, _)⟩,
  rw [set.mem_range] at hx,
  rcases hx with ⟨y, hy⟩,
  rw [←hy],
  exact rayleigh_le_norm T y
end

lemma neg_rayleigh_bdd_above : bdd_above (set.range (-rayleigh_quotient)) :=
begin
  refine set.nonempty_def.mpr ⟨∥T∥, mem_upper_bounds.mpr (λ x hx, _)⟩,
  rw [set.mem_range] at hx,
  rcases hx with ⟨y, hy⟩,
  rw [←hy],
  exact neg_rayleigh_le_norm T y
end

lemma supr_rayleigh_nonneg : (0 : ℝ) ≤ (⨆ x, rayleigh_quotient x) :=
le_csupr_of_le (rayleigh_bdd_above T) 0 (by simp)

lemma supr_neg_rayleigh_nonneg : (0 : ℝ) ≤ (⨆ x, (-rayleigh_quotient) x) :=
le_csupr_of_le (neg_rayleigh_bdd_above T) 0 (by simp)

-- move this
lemma _root_.is_lub_sup_of_is_lub_is_lub {α : Type*} {ι : Sort*} [semilattice_sup α] {f g : ι → α}
  {A B : α} (hf : is_lub (set.range f) A) (hg : is_lub (set.range g) B) :
  is_lub (set.range (λ i, (f i ⊔ g i))) (A ⊔ B) :=
begin
  split,
  { rintros _ ⟨i, rfl⟩,
    exact sup_le_sup (hf.1 ⟨i, rfl⟩) (hg.1 ⟨i, rfl⟩) },
  intros C hC,
  have hfC : C ∈ upper_bounds (set.range f),
  { rintros _ ⟨i, rfl⟩,
    exact le_sup_left.trans (hC ⟨i, rfl⟩) },
  have hgC : C ∈ upper_bounds (set.range g),
  { rintros _ ⟨i, rfl⟩,
    exact le_sup_right.trans (hC ⟨i, rfl⟩) },
  exact sup_le (hf.2 hfC) (hg.2 hgC),
end

-- move this
lemma _root_.csupr_sup_eq {α : Type*} {ι : Sort*} [nonempty ι] [conditionally_complete_lattice α]
  {f g : ι → α} (hf : bdd_above (set.range f)) (hg : bdd_above (set.range g)) :
  (⨆ (x : ι), f x ⊔ g x) = (⨆ (x : ι), f x) ⊔ ⨆ (x : ι), g x :=
by rw (is_lub_sup_of_is_lub_is_lub (is_lub_csupr hf) (is_lub_csupr hg)).csupr_eq

-- move this
lemma _root_.real.csupr_sup_eq {ι : Sort*} {f g : ι → ℝ} (hf : bdd_above (set.range f))
  (hg : bdd_above (set.range g)) :
  (⨆ (x : ι), f x ⊔ g x) = (⨆ (x : ι), f x) ⊔ ⨆ (x : ι), g x :=
begin
  cases is_empty_or_nonempty ι; resetI,
  { simp [real.csupr_empty] },
  exact csupr_sup_eq hf hg,
end

lemma supr_abs_rayleigh_eq_sup_supr :
  (⨆ x : sphere (0:E) 1, |rayleigh_quotient x|) =
    max (⨆ x : sphere (0:E) 1, rayleigh_quotient x)
        (⨆ x : sphere (0:E) 1, -rayleigh_quotient x) :=
begin
  refine real.csupr_sup_eq T.rayleigh_bdd_above_sphere _,
  convert (-T).rayleigh_bdd_above_sphere,
  ext x,
  simp [re_apply_inner_self],
end

lemma abs_rayleigh_sphere_bdd_above :
  bdd_above (set.range (λ x : sphere (0:E) 1, |rayleigh_quotient x|)) :=
begin
  refine set.nonempty_def.mpr ⟨∥T∥, mem_upper_bounds.mpr (λ x hx, _)⟩,
  rw [set.mem_range] at hx,
  rcases hx with ⟨y, hy⟩,
  rw [←hy],
  simp [re_apply_inner_self_apply],
  calc |is_R_or_C.re (⟪T y, y⟫)| ≤ is_R_or_C.abs (⟪T y, y⟫)   : is_R_or_C.abs_re_le_abs _
                            ... ≤ ∥T y∥ * ∥(y : E)∥                 : abs_inner_le_norm _ _
                            ... = ∥T y∥   : by simp [norm_eq_of_mem_sphere y]
                            ... ≤ ∥T∥ * ∥(y : E)∥  : le_op_norm T y
                            ... = ∥T∥     : by simp [norm_eq_of_mem_sphere y]
end

lemma supr_abs_rayleigh_sphere_nonneg [nontrivial E] :
  (0 : ℝ) ≤ (⨆ x : sphere (0:E) 1, |rayleigh_quotient x|) :=
begin
  haveI : nonempty (sphere (0:E) 1) := sphere_nonempty zero_le_one,
  let xs : (sphere (0:E) 1) := nonempty.some (by apply_instance),
  calc (0 : ℝ) ≤ |rayleigh_quotient xs|     : abs_nonneg (rayleigh_quotient xs)
           ... ≤ (⨆ x : sphere (0:E) 1, |rayleigh_quotient x|)   :
             le_csupr_of_le T.abs_rayleigh_sphere_bdd_above xs (le_refl _),
end

lemma re_apply_inner_self_eq_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x = (rayleigh_quotient x) * ∥x∥ ^ 2 :=
begin
  by_cases h : ∥x∥ = 0,
  { rw [norm_eq_zero] at h,
    simp [re_apply_inner_self, h] },
  change ∥x∥ ≠ 0 at h,
  field_simp [re_apply_inner_self],
end

lemma re_apply_inner_self_le_supr_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x ≤ (⨆ z : {x : E // x ≠ 0}, rayleigh_quotient z) * ∥x∥ ^ 2 :=
begin
  by_cases hx : x = 0,
  { simp [hx, re_apply_inner_self] },
  rw [re_apply_inner_self_eq_rayleigh_mul_norm_sq T x],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) 2),
  refine @le_csupr _ {x : E // x ≠ 0} _ (λ z, rayleigh_quotient z) _ ⟨x, hx⟩,
  obtain ⟨C, hC⟩ := rayleigh_bdd_above T,
  use C,
  rintros _ ⟨y, rfl⟩,
  exact hC ⟨y, rfl⟩,
end

lemma re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x ≤
    max (⨆ z : {x : E // x ≠ 0}, rayleigh_quotient z)
      (⨆ z : {x : E // x ≠ 0}, (-rayleigh_quotient) z) * ∥x∥ ^ 2 :=
le_trans (re_apply_inner_self_le_supr_rayleigh_mul_norm_sq T x) $
  mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ∥x∥)

lemma neg_re_apply_inner_self_le_supr_rayleigh_mul_norm_sq (x : E) :
  -T.re_apply_inner_self x ≤ (⨆ z, (-rayleigh_quotient) z) * ∥x∥ ^ 2 :=
begin
  rw [re_apply_inner_self_eq_rayleigh_mul_norm_sq T x],
  simp only [neg_mul_eq_neg_mul],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) 2),
  exact le_csupr (neg_rayleigh_bdd_above T) _,
end

-- the tricky point in general is that for this to be true, the default value taken by the `cSup`
-- function must be 0
lemma _root_.real.csupr_neg {ι : Type*} (f : ι → ℝ) : (⨆ i, - f i) = - ⨅ i, f i :=
begin
  unfold supr,
  unfold infi,
  rw real.Inf_def,
  rw neg_neg,
  congr,
  ext i,
  split,
  { rintros ⟨a, rfl⟩,
    use a,
    simp },
  rw set.mem_neg,
  { rintros ⟨a, ha⟩,
    apply_fun has_neg.neg at ha,
    use a,
    simp [ha] },
end

lemma re_apply_inner_self_le_supr_abs_rayleigh_mul_norm_sq (x : E) :
  T.re_apply_inner_self x ≤ (⨆ z : sphere (0:E) 1, |rayleigh_quotient z|) * ∥x∥ ^ 2 :=
begin
  by_cases hx : x = 0,
  { simp [hx, re_apply_inner_self], },
  simp only [supr_abs_rayleigh_eq_sup_supr],
  have := T.re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq x,
  simp at this,
  refine le_trans this _,
  refine mul_le_mul_of_nonneg_right _ (sq_nonneg _),
  apply max_le_max,
  { rw ← supr_rayleigh_eq_supr_rayleigh_sphere,
    simp },
  { rw [real.csupr_neg, real.csupr_neg, neg_le_neg_iff, ← infi_rayleigh_eq_infi_rayleigh_sphere],
    simp },
end

lemma neg_re_apply_inner_self_le_supr_abs_rayleigh_mul_norm_sq (x : E) :
  -T.re_apply_inner_self x ≤ (⨆ z : sphere (0:E) 1, |rayleigh_quotient z|) * ∥x∥ ^ 2 :=
begin
  convert (-T).re_apply_inner_self_le_supr_abs_rayleigh_mul_norm_sq x,
  { simp [re_apply_inner_self] },
  ext x,
  simp [re_apply_inner_self],
end

lemma neg_re_apply_inner_self_le_max_supr_rayleigh_mul_norm_sq (x : E) :
  -T.re_apply_inner_self x ≤
    max (⨆ z, rayleigh_quotient z) (⨆ z, (-rayleigh_quotient) z) * ∥x∥ ^ 2 :=
le_trans (neg_re_apply_inner_self_le_supr_rayleigh_mul_norm_sq T x) $
  mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ∥x∥)

lemma _root_.is_R_or_C.of_real_mul_inv_re (r : ℝ) (z : 𝕜) :
  is_R_or_C.re ((r : 𝕜)⁻¹ * z) = r⁻¹ * is_R_or_C.re z :=
by rw [←is_R_or_C.of_real_inv, is_R_or_C.of_real_mul_re]

lemma _root_.is_R_or_C.of_real_mul_conj_re (r : ℝ) (z : 𝕜) :
  is_R_or_C.re ((conj (r : 𝕜)) * z) = r * is_R_or_C.re z :=
by simp only [is_R_or_C.conj_of_real, is_R_or_C.mul_re, zero_mul, is_R_or_C.of_real_re, sub_zero,
  is_R_or_C.of_real_im]

lemma _root_.is_R_or_C.of_real_mul_conj_inv_re (r : ℝ) (z : 𝕜) :
  is_R_or_C.re ((conj (r⁻¹ : 𝕜)) * z) = r⁻¹ * is_R_or_C.re z :=
by rw [←is_R_or_C.of_real_inv, is_R_or_C.of_real_mul_conj_re]


end continuous_linear_map

namespace inner_product_space
namespace is_self_adjoint

section general
open continuous_linear_map

variables {T : E →L[𝕜] E}
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2

lemma norm_eq_supr_abs_rayleigh_sphere (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) :
  ∥T∥ = (⨆ x : sphere (0:E) 1, |rayleigh_quotient x|) :=
begin
  rcases subsingleton_or_nontrivial E with h_trivE|h_nontrivE,
  { haveI := h_trivE,
    haveI : is_empty (sphere (0:E) 1) := sphere_is_empty_of_subsingleton one_ne_zero,
    rw [real.csupr_empty, op_norm_subsingleton] },
  haveI := h_nontrivE,
  haveI : nonempty (sphere (0:E) 1) := sphere_nonempty zero_le_one,
  refine op_norm_eq_of_bounds _ (λ x, _) _,
  { exact T.supr_abs_rayleigh_sphere_nonneg },
  { by_cases h_ntriv : T x = 0,
    { simp only [h_ntriv, norm_zero],
      refine mul_nonneg _ (norm_nonneg _),
      exact T.supr_abs_rayleigh_sphere_nonneg },
    set L := real.sqrt (∥T x∥ / ∥x∥) with hL,
    set rT := ⨆ z : sphere (0:E) 1, |rayleigh_quotient z|,
    set x₁ := (L : 𝕜) • x + (L⁻¹ : 𝕜) • (T x) with hx₁,
    set x₂ := (L : 𝕜) • x - (L⁻¹ : 𝕜) • (T x) with hx₂,
    change T x ≠ 0 at h_ntriv,
    have hTx_ntriv : ∥T x∥ ≠ 0 := λ H, by { rw [norm_eq_zero] at H, exact h_ntriv H },
    have hx_ntriv : ∥x∥ ≠ 0,
    { intro H,
      rw [norm_eq_zero] at H,
      rw [H] at h_ntriv,
      exact h_ntriv (map_zero _) },
    have hL_nonneg : 0 ≤ L := real.sqrt_nonneg _,
    have hLinv_nonneg : 0 ≤ L⁻¹ := inv_nonneg.mpr hL_nonneg,
    have hL_sq : L^2 = ∥T x∥ / ∥x∥ := real.sq_sqrt (div_nonneg (norm_nonneg _) (norm_nonneg _)),
    have hLinv_sq_nonneg : 0 ≤ ∥x∥ / ∥T x∥ := div_nonneg (norm_nonneg _) (norm_nonneg _),
    have hL_sq_nonneg : 0 ≤ ∥T x∥ / ∥x∥ := div_nonneg (norm_nonneg _) (norm_nonneg _),
    have hLinv_sq : (L⁻¹)^2 = ∥x∥ / ∥T x∥,
    { simp only [←real.sqrt_inv, inv_div],
      rw [real.sq_sqrt hLinv_sq_nonneg] },
    have hL_ntriv : L ≠ 0,
    { intro H,
      rw [real.sqrt_eq_zero hL_sq_nonneg, div_eq_zero_iff] at H,
      exact or.elim H hTx_ntriv hx_ntriv },
    have hL_mul₁ : L * L⁻¹ = 1 := mul_inv_cancel hL_ntriv,
    have hL_mul₂ : L⁻¹ * L = 1 := (mul_comm L L⁻¹) ▸ hL_mul₁,
    have gizmo : ⟪T (T x), x⟫ = ⟪T x, T x⟫ := hT _ _,
    have h₁ : T.re_apply_inner_self x₁ - T.re_apply_inner_self x₂ = 4 * ∥T x∥ ^ 2,
    { simp only [hx₁, hx₂, re_apply_inner_self_apply, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, ←inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
        hL_mul₁, hL_mul₂, is_R_or_C.of_real_mul_re, is_R_or_C.re.map_add, is_R_or_C.re.map_sub,
        is_R_or_C.of_real_mul_inv_re, continuous_linear_map.map_add, continuous_linear_map.map_sub,
        continuous_linear_map.map_smul, is_R_or_C.of_real_mul_conj_re,
        is_R_or_C.of_real_mul_conj_inv_re, gizmo],
      ring_nf,
      field_simp },
    have h₄ : T.re_apply_inner_self x₁ ≤ rT * ∥x₁∥^2 :=
      re_apply_inner_self_le_supr_abs_rayleigh_mul_norm_sq _ _,
    have h₅ : -T.re_apply_inner_self x₂ ≤ rT * ∥x₂∥^2 :=
      neg_re_apply_inner_self_le_supr_abs_rayleigh_mul_norm_sq _ _,
    have h₆ := calc
      4 * ∥T x∥^2 ≤ rT * ∥x₁∥^2 + rT * ∥x₂∥^2          :
        by { rw [←h₁, sub_eq_add_neg], exact add_le_add h₄ h₅ }
             ...  = rT * (∥x₁∥ * ∥x₁∥) + rT * (∥x₂∥ * ∥x₂∥)      : by simp only [pow_two]
             ...  = rT * (∥x₁∥ * ∥x₁∥ + ∥x₂∥ * ∥x₂∥)     : by ring
             ...  = rT * (2 * (L^2 * ∥x∥ * ∥x∥ + (L⁻¹)^2 * ∥T x∥ * ∥T x∥)) :
              begin
                simp only [parallelogram_law_with_norm, norm_smul, is_R_or_C.norm_of_real,
                           real.norm_of_nonneg hL_nonneg, real.norm_of_nonneg hLinv_nonneg,
                           ←is_R_or_C.of_real_inv],
                ring
              end
             ...  = 4 * rT * ∥T x∥ * ∥x∥  :
              begin
                simp only [hL_sq, hLinv_sq],
                field_simp,
                ring
              end,
    have h₇ : 0 < 4 * ∥T x∥ := mul_pos (by norm_num) (norm_pos_iff.mpr h_ntriv),
    rw [←mul_le_mul_left h₇],
    calc 4 * ∥T x∥ * ∥T x∥ = 4 * ∥T x∥ ^ 2          : by rw [mul_assoc, ←pow_two]
                      ... ≤ 4 * rT * ∥T x∥ * ∥x∥   : h₆
                      ... = _                      : by ring },
  { intros N hN h,
    refine csupr_le (λ x, _),
    have hx : ∥(x : E)∥ = 1 := norm_eq_of_mem_sphere x,
    simp [hx, re_apply_inner_self],
    calc _ ≤ is_R_or_C.abs (⟪T x, x⟫)       : is_R_or_C.abs_re_le_abs _
       ... ≤ ∥T x∥ * ∥(x:E)∥      : abs_inner_le_norm _ _
       ... = ∥T x∥            : by simp [hx]
       ... ≤ N * ∥(x:E)∥     : h x
       ... = N               : by simp [hx] }
end

end general

section real
variables {F : Type*} [inner_product_space ℝ F]

lemma has_strict_fderiv_at_re_apply_inner_self
  {T : F →L[ℝ] F} (hT : is_self_adjoint (T : F →ₗ[ℝ] F)) (x₀ : F) :
  has_strict_fderiv_at T.re_apply_inner_self (bit0 (innerSL (T x₀))) x₀ :=
begin
  convert T.has_strict_fderiv_at.inner (has_strict_fderiv_at_id x₀),
  ext y,
  simp [bit0, hT.apply_clm x₀ y, real_inner_comm x₀]
end

variables [complete_space F] {T : F →L[ℝ] F}
local notation `rayleigh_quotient` := λ x : F, T.re_apply_inner_self x / ∥(x:F)∥ ^ 2

lemma linearly_dependent_of_is_local_extr_on (hT : is_self_adjoint (T : F →ₗ[ℝ] F))
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ∥x₀∥) x₀) :
  ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 :=
begin
  have H : is_local_extr_on T.re_apply_inner_self {x : F | ∥x∥ ^ 2 = ∥x₀∥ ^ 2} x₀,
  { convert hextr,
    ext x,
    simp [dist_eq_norm] },
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `λ x, ∥x∥ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ := is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d H
    (has_strict_fderiv_at_norm_sq x₀) (hT.has_strict_fderiv_at_re_apply_inner_self x₀),
  refine ⟨a, b, h₁, _⟩,
  apply (inner_product_space.to_dual_map ℝ F).injective,
  simp only [linear_isometry.map_add, linear_isometry.map_smul, linear_isometry.map_zero],
  change a • innerSL x₀ + b • innerSL (T x₀) = 0,
  apply smul_right_injective (F →L[ℝ] ℝ) (two_ne_zero : (2:ℝ) ≠ 0),
  simpa only [bit0, add_smul, smul_add, one_smul, add_zero] using h₂
end

lemma eq_smul_self_of_is_local_extr_on_real (hT : is_self_adjoint (T : F →ₗ[ℝ] F))
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ∥x₀∥) x₀) :
  T x₀ = (rayleigh_quotient x₀) • x₀ :=
begin
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_is_local_extr_on hextr,
  by_cases hx₀ : x₀ = 0,
  { simp [hx₀] },
  by_cases hb : b = 0,
  { have : a ≠ 0 := by simpa [hb] using h₁,
    refine absurd _ hx₀,
    apply smul_right_injective F this,
    simpa [hb] using h₂ },
  let c : ℝ := - b⁻¹ * a,
  have hc : T x₀ = c • x₀,
  { have : b * (b⁻¹ * a) = a := by field_simp [mul_comm],
    apply smul_right_injective F hb,
    simp [c, ← neg_eq_of_add_eq_zero h₂, ← mul_smul, this] },
  convert hc,
  have : ∥x₀∥ ≠ 0 := by simp [hx₀],
  field_simp,
  simpa [inner_smul_left, real_inner_self_eq_norm_mul_norm, sq] using congr_arg (λ x, ⟪x, x₀⟫_ℝ) hc,
end

end real

section complete_space
variables [complete_space E] {T : E →L[𝕜] E}
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2

lemma eq_smul_self_of_is_local_extr_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  T x₀ = (↑(rayleigh_quotient x₀) : 𝕜) • x₀ :=
begin
  letI := inner_product_space.is_R_or_C_to_real 𝕜 E,
  let S : E →L[ℝ] E :=
    @continuous_linear_map.restrict_scalars 𝕜 E E _ _ _ _ _ _ _ ℝ _ _ _ _ T,
  have hSA : is_self_adjoint (S : E →ₗ[ℝ] E) := λ x y, by
  { have := hT x y,
    simp only [continuous_linear_map.coe_coe] at this,
    simp only [real_inner_eq_re_inner, this, continuous_linear_map.coe_restrict_scalars,
      continuous_linear_map.coe_coe, linear_map.coe_restrict_scalars_eq_coe] },
  exact eq_smul_self_of_is_local_extr_on_real hSA hextr,
end

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
lemma has_eigenvector_of_is_local_extr_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(rayleigh_quotient x₀) x₀ :=
begin
  refine ⟨_, hx₀⟩,
  rw module.End.mem_eigenspace_iff,
  exact hT.eq_smul_self_of_is_local_extr_on hextr
end

/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_max_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_max_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(⨆ x : {x : E // x ≠ 0}, rayleigh_quotient x) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inr hextr.localize),
  have hx₀' : 0 < ∥x₀∥ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (∥x₀∥) := by simp,
  rw T.supr_rayleigh_eq_supr_rayleigh_sphere hx₀',
  refine is_max_on.supr_eq hx₀'' _,
  intros x hx,
  dsimp,
  have : ∥x∥ = ∥x₀∥ := by simpa using hx,
  rw this,
  exact div_le_div_of_le (sq_nonneg ∥x₀∥) (hextr hx)
end

/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_min_on (hT : is_self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_min_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(⨅ x : {x : E // x ≠ 0}, rayleigh_quotient x) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inl hextr.localize),
  have hx₀' : 0 < ∥x₀∥ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (∥x₀∥) := by simp,
  rw T.infi_rayleigh_eq_infi_rayleigh_sphere hx₀',
  refine is_min_on.infi_eq hx₀'' _,
  intros x hx,
  dsimp,
  have : ∥x∥ = ∥x₀∥ := by simpa using hx,
  rw this,
  exact div_le_div_of_le (sq_nonneg ∥x₀∥) (hextr hx)
end

end complete_space

section compact
variables {T : E →L[𝕜] E}

local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2
local notation `rayleigh_quotient_sphere` :=
λ x : sphere (0:E) 1, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2
local notation `u_sph` := sphere (0:E) 1
lemma exists_eigenvalue_of_compact_aux [nontrivial E]
  (hT_cpct : compact_map T) (h_pos_case : ∥T∥ = (⨆ x : sphere (0:E) 1, rayleigh_quotient x)) :
  ∃ c, has_eigenvalue (T : E →ₗ[𝕜] E) c :=
begin
  haveI : nonempty (sphere (0:E) 1) := continuous_linear_map.sphere_nonempty zero_le_one,
  by_cases h_triv : T = 0,
  { rcases exists_ne (0 : E) with ⟨w, hw⟩,
    refine ⟨0, has_eigenvalue_of_has_eigenvector ⟨_, hw⟩⟩,
    simp only [mem_eigenspace_iff, h_triv, zero_smul, continuous_linear_map.to_linear_map_eq_coe,
      continuous_linear_map.coe_zero, linear_map.zero_apply] },
  { change T ≠ 0 at h_triv,
    have nT_ne_zero : ∥T∥ ≠ 0 := norm_ne_zero_iff.mpr h_triv,
    refine ⟨∥T∥, _⟩,
    set l₁ : filter u_sph :=
      filter.comap rayleigh_quotient_sphere (𝓝[set.range rayleigh_quotient_sphere] ∥T∥),
    set l₂ : filter E := l₁.map (λ x : u_sph, T x),
    have h_bdd_range : bdd_above (set.range rayleigh_quotient_sphere) :=
      T.rayleigh_bdd_above_sphere,
    have h_range_nonempty : (set.range rayleigh_quotient_sphere).nonempty,
    { exact set.range_nonempty _ },
    have h_ne_bot : (𝓝[set.range rayleigh_quotient_sphere] ∥T∥).ne_bot,
    { simp_rw [h_pos_case],
      exact is_lub.nhds_within_ne_bot (is_lub_csupr h_bdd_range) h_range_nonempty },
    have hl₂ : l₂ ≤ 𝓟 (closure (T '' u_sph)) := by
    { refine le_trans _ (filter.monotone_principal subset_closure),
      have : T '' u_sph = set.range (λ x : u_sph, T x),
      { ext, simp only [exists_prop, set.mem_range, set.mem_image, set_coe.exists, subtype.coe_mk]},
      rw [this, filter.map_le_iff_le_comap, filter.comap_principal],
      simp only [le_top, filter.principal_univ, set.preimage_range] },
    haveI : l₁.ne_bot := filter.ne_bot.comap_of_range_mem h_ne_bot self_mem_nhds_within,
    -- The image of T on the sphere is compact since T is a compact operator
    have h_img_cpct : is_compact (closure (T '' u_sph)) := hT_cpct _ bounded_sphere,
    -- l₂ is guaranteed to have a cluster point z for some vector z by compactness of T
    have hl₂' := h_img_cpct hl₂,
    rcases hl₂' with ⟨z, ⟨hz₁, hz₂⟩⟩,
    set l₁sub : filter u_sph := l₁ ⊓ (𝓝 z ⊓ l₂).comap (λ x, T x),
    haveI : l₁sub.ne_bot,
    { simp only [←filter.map_ne_bot_iff (λ x : u_sph, T x), l₁sub, filter.push_pull, ←l₂, inf_comm],
      simp_rw [←inf_assoc, inf_idem],
      rw [inf_comm],
      exact hz₂.ne_bot },
    have h_premain₂ : l₁sub.tendsto (λ y, is_R_or_C.re (⟪T y, y⟫)) (𝓝 ∥T∥),
    { simp_rw [←T.rayleigh_sphere_eq],
      calc l₁sub.map rayleigh_quotient_sphere
            ≤ l₁.map rayleigh_quotient_sphere
            : filter.map_mono inf_le_left
        ... = (𝓝[set.range rayleigh_quotient_sphere] (∥T∥)) ⊓ 𝓟 (set.range rayleigh_quotient_sphere)
            : filter.map_comap _ _
        ... ≤ (𝓝[set.range rayleigh_quotient_sphere] (∥T∥))
            : inf_le_left
        ... ≤ 𝓝 (∥T∥)   : nhds_within_le_nhds },
    have h_premain : l₁sub.tendsto (λ y, T y) (𝓝 z),
    { refine filter.tendsto.mono_left _ inf_le_right,
      simp only [filter.tendsto, filter.map_comap, inf_assoc, inf_le_left] },
    have h_main : l₁sub.tendsto (λ y : u_sph, (∥T∥ : 𝕜) • (y : E)) (𝓝 z),
    { refine tendsto_of_tendsto_of_dist h_premain _,
      simp only [dist_eq_norm],
      have h₁₂ : (λ x : u_sph, ∥T x - (∥T∥ : 𝕜) • x∥) =
        (λ x : u_sph, real.sqrt (∥T x - (∥T∥ : 𝕜) • x∥ ^ 2)),
      { simp_rw [real.sqrt_sq (norm_nonneg _)] },
      rw [h₁₂, ←real.sqrt_zero],
      refine filter.tendsto.sqrt _,
      -- Main calculation from Einsiedler-Ward
      have h_squeeze : ∀ y : u_sph,
        ∥T y - (∥T∥ : 𝕜) • y∥ ^ 2 ≤ 2 * ∥T∥^2 - 2 * ∥T∥ * is_R_or_C.re (⟪T y, y⟫),
      { intros y,
        calc ∥T y - (∥T∥ : 𝕜) • y∥ ^ 2 =
               ∥T y∥^2 - 2 * ∥T∥ * is_R_or_C.re (⟪T y, y⟫) + ∥(∥T∥ : 𝕜) • (y : E)∥^2
                  : by { simp_rw [norm_sub_sq, norm_smul, inner_smul_right,
                                  is_R_or_C.of_real_mul_re], ring }
           ... ≤ ∥T y∥^2 - 2 * ∥T∥ * is_R_or_C.re (⟪T y, y⟫) + ∥T∥ ^ 2
                  : by { refine add_le_add_left _ _, simp [norm_smul] }
           ... ≤ ∥T∥^2 - 2 * ∥T∥ * is_R_or_C.re (⟪T y, y⟫) + ∥T∥ ^ 2
                  : begin
                      refine add_le_add_right _ _,
                      refine sub_le_sub_right _ _,
                      refine pow_le_pow_of_le_left (norm_nonneg _) _ 2,
                      calc ∥T y∥ ≤ ∥T∥ * ∥(y : E)∥    : T.le_op_norm _
                           ...   = ∥T∥                : by rw [norm_eq_of_mem_sphere y, mul_one]
                    end
           ... ≤ _
                  : by ring_nf },
      refine squeeze_zero (λ y, pow_two_nonneg _) h_squeeze _,
      have h_bs : 2 * ∥T∥^2 - 2 * ∥T∥^2 = 0 := by ring,
      rw [←h_bs],
      refine filter.tendsto.const_sub _ _,
      rw [pow_two, ←mul_assoc],
      refine filter.tendsto.const_mul _ h_premain₂ },
    have hz_norm : ∥z∥ = ∥T∥,
    { have := h_main.norm,
      have h_smul : (λ y : u_sph, ∥(∥T∥ : 𝕜) • (y : E)∥) = λ y, ∥T∥,
      { ext, simp [norm_smul] },
      simp [h_smul] at this,
      refine eq.symm _,
      refine tendsto_nhds_unique tendsto_const_nhds this },
    have z_ne_zero : z ≠ 0,
    { rintro hz_zero,
      rw [hz_zero, norm_zero] at hz_norm,
      exact nT_ne_zero hz_norm.symm },
    let zs : u_sph := ⟨(∥z∥⁻¹ : 𝕜) • z, by rw [mem_sphere, dist_eq_norm, sub_zero,
                                              norm_smul_inv_norm z_ne_zero]⟩,
    have h₂ : (∥T∥ : 𝕜) • (zs : E) = z,
    { have : (∥z∥ : 𝕜) ≠ 0 := by { norm_cast, exact norm_ne_zero_iff.mpr z_ne_zero },
      simp only [←hz_norm, smul_smul, mul_inv_cancel this, one_smul, subtype.coe_mk] },
    have h₃ : (zs : E) ≠ 0 := ne_zero_of_mem_unit_sphere zs,
    have hzs : (∥T∥⁻¹ : 𝕜) • z = zs,
    { simp only [hz_norm, subtype.coe_mk]},
    have h₄ : l₁sub ≤ 𝓝 zs,
    { have h_main' := filter.tendsto.const_smul h_main (∥T∥⁻¹ : 𝕜),
      have a_ne_zero' : (∥T∥ : 𝕜) ≠ 0 := by simp [nT_ne_zero],
      simp only [smul_smul, inv_mul_cancel a_ne_zero', filter.tendsto_iff_comap, hzs, one_smul]
        at h_main',
      convert h_main',
      exact nhds_subtype_eq_comap },
    refine has_eigenvalue_of_has_eigenvector ⟨_, h₃⟩,
    rw [mem_eigenspace_iff, h₂],
    refine tendsto_nhds_unique _ h_premain,
    refine filter.tendsto.mono_left _ h₄,
    have Tsph_cont : continuous (λ x : u_sph, T x) :=
      continuous.comp T.continuous continuous_subtype_coe,
    exact Tsph_cont.tendsto _ }
end

-- move this
lemma _root_.inner_product_space.is_self_adjoint.neg {𝕜 : Type u_1} {E : Type u_2} [is_R_or_C 𝕜]
  [inner_product_space 𝕜 E] {T : E →ₗ[𝕜] E} (hT : is_self_adjoint T) :
  is_self_adjoint (-T) :=
begin
  intros x y,
  simpa [inner_neg_left, inner_neg_right] using congr_arg (λ a, -a) (hT x y),
end

lemma exists_eigenvalue_of_compact [nontrivial E] (hT : is_self_adjoint (T : E →ₗ[𝕜] E))
  (hT_cpct : compact_map T) : ∃ c, has_eigenvalue (T : E →ₗ[𝕜] E) c :=
begin
  have H₁ := hT.norm_eq_supr_abs_rayleigh_sphere,
  rw T.supr_abs_rayleigh_eq_sup_supr at H₁,
  rcases max_cases (⨆ (x : ↥(sphere (0:E) 1)), (λ (x : E), T.re_apply_inner_self x / ∥x∥ ^ 2) x)
                    (⨆ (x : ↥(sphere (0:E) 1)), -(λ (x : E), T.re_apply_inner_self x / ∥x∥ ^ 2) x)
                    with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩,
  { rw h₁ at H₁,
    exact exists_eigenvalue_of_compact_aux hT_cpct H₁ },
  { rw h₁ at H₁,
    have : is_self_adjoint (↑(-T) : E →ₗ[𝕜] E) := hT.neg,
    obtain ⟨c, hc⟩ := @exists_eigenvalue_of_compact_aux _ _ _ _ (-T) _ hT_cpct.neg _,
    { use -c,
      rw has_eigenvalue at hc ⊢,
      convert hc using 1,
      ext x,
      simp [mem_eigenspace_iff, neg_eq_iff_add_eq_zero, eq_neg_iff_add_eq_zero] },
    convert H₁ using 1,
    { simp },
    congr,
    ext x,
    simp [continuous_linear_map.re_apply_inner_self] },
end

lemma subsingleton_of_no_eigenvalue_of_compact (hT : is_self_adjoint (T : E →ₗ[𝕜] E))
  (hT_cpct : compact_map T) (hT' : ∀ μ : 𝕜, module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) :
  subsingleton E :=
(subsingleton_or_nontrivial E).resolve_right
  (λ h, by exactI absurd (hT' _) (hT.exists_eigenvalue_of_compact hT_cpct).some_spec)

end compact


section finite_dimensional
variables [finite_dimensional 𝕜 E] [_i : nontrivial E] {T : E →ₗ[𝕜] E}

include _i

/-- The supremum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_supr_of_finite_dimensional (hT : is_self_adjoint T) :
  has_eigenvalue T ↑(⨆ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ∥(x:E)∥ ^ 2) :=
begin
  haveI := finite_dimensional.proper_is_R_or_C 𝕜 E,
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : is_self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_ge H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_max_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  exact has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_max_on hx₀_ne this)
end

/-- The infimum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_infi_of_finite_dimensional (hT : is_self_adjoint T) :
  has_eigenvalue T ↑(⨅ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ∥(x:E)∥ ^ 2) :=
begin
  haveI := finite_dimensional.proper_is_R_or_C 𝕜 E,
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : is_self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_le H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_min_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  exact has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_min_on hx₀_ne this)
end

omit _i

lemma subsingleton_of_no_eigenvalue_finite_dimensional
  (hT : is_self_adjoint T) (hT' : ∀ μ : 𝕜, module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) :
  subsingleton E :=
(subsingleton_or_nontrivial E).resolve_right
  (λ h, by exactI absurd (hT' _) hT.has_eigenvalue_supr_of_finite_dimensional)

end finite_dimensional

end is_self_adjoint
end inner_product_space

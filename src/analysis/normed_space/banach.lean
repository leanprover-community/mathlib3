/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.baire
import analysis.normed_space.operator_norm

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

open function metric set filter finset
open_locale classical topological_space big_operators

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
(f : E →L[𝕜] F)
include 𝕜


variable [complete_space F]

/--
First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ∥y∥`.
For further use, we will only need such an element whose image
is within distance `∥y∥/2` of `y`, to apply an iterative process. -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma exists_approx_preimage_norm_le (surj : surjective f) :
  ∃C ≥ 0, ∀y, ∃x, dist (f x) y ≤ 1/2 * ∥y∥ ∧ ∥x∥ ≤ C * ∥y∥ :=
begin
  have A : (⋃n:ℕ, closure (f '' (ball 0 n))) = univ,
  { refine subset.antisymm (subset_univ _) (λy hy, _),
    rcases surj y with ⟨x, hx⟩,
    rcases exists_nat_gt (∥x∥) with ⟨n, hn⟩,
    refine mem_Union.2 ⟨n, subset_closure _⟩,
    refine (mem_image _ _ _).2 ⟨x, ⟨_, hx⟩⟩,
    rwa [mem_ball, dist_eq_norm, sub_zero] },
  have : ∃ (n : ℕ) x, x ∈ interior (closure (f '' (ball 0 n))) :=
    nonempty_interior_of_Union_of_closed (λn, is_closed_closure) A,
  simp only [mem_interior_iff_mem_nhds, mem_nhds_iff] at this,
  rcases this with ⟨n, a, ε, ⟨εpos, H⟩⟩,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine ⟨(ε/2)⁻¹ * ∥c∥ * 2 * n, _, λy, _⟩,
  { refine mul_nonneg (mul_nonneg (mul_nonneg _ (norm_nonneg _)) (by norm_num)) _,
    refine inv_nonneg.2 (div_nonneg' (le_of_lt εpos) (by norm_num)),
    exact nat.cast_nonneg n },
  { by_cases hy : y = 0,
    { use 0, simp [hy] },
    { rcases rescale_to_shell hc (half_pos εpos) hy with ⟨d, hd, ydle, leyd, dinv⟩,
      let δ := ∥d∥ * ∥y∥/4,
      have δpos : 0 < δ :=
        div_pos (mul_pos (norm_pos_iff.2 hd) (norm_pos_iff.2 hy)) (by norm_num),
      have : a + d • y ∈ ball a ε,
        by simp [dist_eq_norm, lt_of_le_of_lt ydle (half_lt_self εpos)],
      rcases metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩,
      rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩,
      rw ← xz₁ at h₁,
      rw [mem_ball, dist_eq_norm, sub_zero] at hx₁,
      have : a ∈ ball a ε, by { simp, exact εpos },
      rcases metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩,
      rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩,
      rw ← xz₂ at h₂,
      rw [mem_ball, dist_eq_norm, sub_zero] at hx₂,
      let x := x₁ - x₂,
      have I : ∥f x - d • y∥ ≤ 2 * δ := calc
        ∥f x - d • y∥ = ∥f x₁ - (a + d • y) - (f x₂ - a)∥ :
          by { congr' 1, simp only [x, f.map_sub], abel }
        ... ≤ ∥f x₁ - (a + d • y)∥ + ∥f x₂ - a∥ :
          norm_sub_le _ _
        ... ≤ δ + δ : begin
            apply add_le_add,
            { rw [← dist_eq_norm, dist_comm], exact le_of_lt h₁ },
            { rw [← dist_eq_norm, dist_comm], exact le_of_lt h₂ }
          end
        ... = 2 * δ : (two_mul _).symm,
      have J : ∥f (d⁻¹ • x) - y∥ ≤ 1/2 * ∥y∥ := calc
        ∥f (d⁻¹ • x) - y∥ = ∥d⁻¹ • f x - (d⁻¹ * d) • y∥ :
          by rwa [f.map_smul _, inv_mul_cancel, one_smul]
        ... = ∥d⁻¹ • (f x - d • y)∥ : by rw [mul_smul, smul_sub]
        ... = ∥d∥⁻¹ * ∥f x - d • y∥ : by rw [norm_smul, normed_field.norm_inv]
        ... ≤ ∥d∥⁻¹ * (2 * δ) : begin
            apply mul_le_mul_of_nonneg_left I,
            rw inv_nonneg,
            exact norm_nonneg _
          end
        ... = (∥d∥⁻¹ * ∥d∥) * ∥y∥ /2 : by { simp only [δ], ring }
        ... = ∥y∥/2 : by { rw [inv_mul_cancel, one_mul],  simp [norm_eq_zero, hd] }
        ... = (1/2) * ∥y∥ : by ring,
      rw ← dist_eq_norm at J,
      have 𝕜 : ∥d⁻¹ • x∥ ≤ (ε / 2)⁻¹ * ∥c∥ * 2 * ↑n * ∥y∥ := calc
        ∥d⁻¹ • x∥ = ∥d∥⁻¹ * ∥x₁ - x₂∥ : by rw [norm_smul, normed_field.norm_inv]
        ... ≤ ((ε / 2)⁻¹ * ∥c∥ * ∥y∥) * (n + n) : begin
            refine mul_le_mul dinv _ (norm_nonneg _) _,
            { exact le_trans (norm_sub_le _ _) (add_le_add (le_of_lt hx₁) (le_of_lt hx₂)) },
            { apply mul_nonneg (mul_nonneg _ (norm_nonneg _)) (norm_nonneg _),
              exact inv_nonneg.2 (le_of_lt (half_pos εpos)) }
          end
        ... = (ε / 2)⁻¹ * ∥c∥ * 2 * ↑n * ∥y∥ : by ring,
      exact ⟨d⁻¹ • x, J, 𝕜⟩ } },
end

variable [complete_space E]

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem exists_preimage_norm_le (surj : surjective f) :
  ∃C > 0, ∀y, ∃x, f x = y ∧ ∥x∥ ≤ C * ∥y∥ :=
begin
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj,
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
  the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
  has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
  leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
  of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
  preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC,
  let h := λy, y - f (g y),
  have hle : ∀y, ∥h y∥ ≤ (1/2) * ∥y∥,
  { assume y,
    rw [← dist_eq_norm, dist_comm],
    exact (hg y).1 },
  refine ⟨2 * C + 1, by linarith, λy, _⟩,
  have hnle : ∀n:ℕ, ∥(h^[n]) y∥ ≤ (1/2)^n * ∥y∥,
  { assume n,
    induction n with n IH,
    { simp only [one_div_eq_inv, nat.nat_zero_eq_zero, one_mul, iterate_zero_apply,
        pow_zero] },
    { rw [iterate_succ'],
      apply le_trans (hle _) _,
      rw [pow_succ, mul_assoc],
      apply mul_le_mul_of_nonneg_left IH,
      norm_num } },
  let u := λn, g((h^[n]) y),
  have ule : ∀n, ∥u n∥ ≤ (1/2)^n * (C * ∥y∥),
  { assume n,
    apply le_trans (hg _).2 _,
    calc C * ∥(h^[n]) y∥ ≤ C * ((1/2)^n * ∥y∥) : mul_le_mul_of_nonneg_left (hnle n) C0
         ... = (1 / 2) ^ n * (C * ∥y∥) : by ring },
  have sNu : summable (λn, ∥u n∥),
  { refine summable_of_nonneg_of_le (λn, norm_nonneg _) ule _,
    exact summable.mul_right _ (summable_geometric_of_lt_1 (by norm_num) (by norm_num)) },
  have su : summable u := summable_of_summable_norm sNu,
  let x := tsum u,
  have x_ineq : ∥x∥ ≤ (2 * C + 1) * ∥y∥ := calc
    ∥x∥ ≤ (∑'n, ∥u n∥) : norm_tsum_le_tsum_norm sNu
    ... ≤ (∑'n, (1/2)^n * (C * ∥y∥)) :
      tsum_le_tsum ule sNu (summable.mul_right _ summable_geometric_two)
    ... = (∑'n, (1/2)^n) * (C * ∥y∥) : by { rw tsum_mul_right, exact summable_geometric_two }
    ... = 2 * (C * ∥y∥) : by rw tsum_geometric_two
    ... = 2 * C * ∥y∥ + 0 : by rw [add_zero, mul_assoc]
    ... ≤ 2 * C * ∥y∥ + ∥y∥ : add_le_add (le_refl _) (norm_nonneg _)
    ... = (2 * C + 1) * ∥y∥ : by ring,
  have fsumeq : ∀n:ℕ, f(∑ i in finset.range n, u i) = y - (h^[n]) y,
  { assume n,
    induction n with n IH,
    { simp [f.map_zero] },
    { rw [sum_range_succ, f.map_add, IH, iterate_succ'],
      simp [u, h, sub_eq_add_neg, add_comm, add_left_comm] } },
  have : tendsto (λn, ∑ i in range n, u i) at_top (𝓝 x) :=
    su.has_sum.tendsto_sum_nat,
  have L₁ : tendsto (λn, f(∑ i in range n, u i)) at_top (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this,
  simp only [fsumeq] at L₁,
  have L₂ : tendsto (λn, y - (h^[n]) y) at_top (𝓝 (y - 0)),
  { refine tendsto_const_nhds.sub _,
    rw tendsto_iff_norm_tendsto_zero,
    simp only [sub_zero],
    refine squeeze_zero (λ_, norm_nonneg _) hnle _,
    have : 0 = 0 * ∥y∥, by rw zero_mul,
    rw this,
    refine tendsto.mul _ tendsto_const_nhds,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (by norm_num) (by norm_num) },
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂,
  rw sub_zero at feq,
  exact ⟨x, feq, x_ineq⟩
end

/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is open. -/
theorem open_mapping (surj : surjective f) : is_open_map f :=
begin
  assume s hs,
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩,
  refine is_open_iff.2 (λy yfs, _),
  rcases mem_image_iff_bex.1 yfs with ⟨x, xs, fxy⟩,
  rcases is_open_iff.1 hs x xs with ⟨ε, εpos, hε⟩,
  refine ⟨ε/C, div_pos εpos Cpos, λz hz, _⟩,
  rcases hC (z-y) with ⟨w, wim, wnorm⟩,
  have : f (x + w) = z, by { rw [f.map_add, wim, fxy, add_sub_cancel'_right] },
  rw ← this,
  have : x + w ∈ ball x ε := calc
    dist (x+w) x = ∥w∥ : by { rw dist_eq_norm, simp }
    ... ≤ C * ∥z - y∥ : wnorm
    ... < C * (ε/C) : begin
        apply mul_lt_mul_of_pos_left _ Cpos,
        rwa [mem_ball, dist_eq_norm] at hz,
      end
    ... = ε : mul_div_cancel' _ (ne_of_gt Cpos),
  exact set.mem_image_of_mem _ (hε this)
end

namespace linear_equiv

/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
theorem continuous_symm (e : E ≃ₗ[𝕜] F) (h : continuous e) :
  continuous e.symm :=
begin
  intros s hs,
  rw [← e.image_eq_preimage],
  rw [← e.coe_coe] at h ⊢,
  exact open_mapping ⟨↑e, h⟩ e.surjective s hs
end

/-- Associating to a linear equivalence between Banach spaces a continuous linear equivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ensures that the
inverse map is also continuous. -/
def to_continuous_linear_equiv_of_continuous (e : E ≃ₗ[𝕜] F) (h : continuous e) :
  E ≃L[𝕜] F :=
{ continuous_to_fun := h,
  continuous_inv_fun := e.continuous_symm h,
  ..e }

@[simp] lemma coe_fn_to_continuous_linear_equiv_of_continuous (e : E ≃ₗ[𝕜] F) (h : continuous e) :
  ⇑(e.to_continuous_linear_equiv_of_continuous h) = e := rfl

@[simp] lemma coe_fn_to_continuous_linear_equiv_of_continuous_symm (e : E ≃ₗ[𝕜] F)
  (h : continuous e) :
  ⇑(e.to_continuous_linear_equiv_of_continuous h).symm = e.symm := rfl

end linear_equiv

namespace continuous_linear_equiv

/-- Convert a bijective continuous linear map `f : E →L[𝕜] F` between two Banach spaces
to a continuous linear equivalence. -/
noncomputable def of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
  E ≃L[𝕜] F :=
(linear_equiv.of_bijective ↑f hinj hsurj).to_continuous_linear_equiv_of_continuous f.continuous

@[simp] lemma coe_fn_of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
  ⇑(of_bijective f hinj hsurj) = f := rfl

@[simp] lemma of_bijective_symm_apply_apply (f : E →L[𝕜] F) (hinj : f.ker = ⊥)
  (hsurj : f.range = ⊤) (x : E) :
  (of_bijective f hinj hsurj).symm (f x) = x :=
(of_bijective f hinj hsurj).symm_apply_apply x

@[simp] lemma of_bijective_apply_symm_apply (f : E →L[𝕜] F) (hinj : f.ker = ⊥)
  (hsurj : f.range = ⊤) (y : F) :
  f ((of_bijective f hinj hsurj).symm y) = y :=
(of_bijective f hinj hsurj).apply_symm_apply y

end continuous_linear_equiv

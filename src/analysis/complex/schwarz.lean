/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.abs_max
import analysis.complex.removable_singularity

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `complex.norm_deriv_le_div_of_maps_to_ball`, `complex.abs_deriv_le_div_of_maps_to_ball`: if
  `f : ℂ → E` sends an open disk with center `c` and a positive radius `R₁` to an open ball with
  center `f c` and radius `R₂`, then the absolute value of the derivative of `f` at `c` is at most
  the ratio `R₂ / R₁`;

* `complex.dist_le_div_mul_dist_of_maps_to_ball`: if `f : ℂ → E` sends an open disk with center `c`
  and radius `R₁` to an open disk with center `f c` and radius `R₂`, then for any `z` in the former
  disk we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`;

* `complex.abs_deriv_le_one_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk of positive radius
  to itself and the center of this disk to itself, then the absolute value of the derivative of `f`
  at the center of this disk is at most `1`;

* `complex.dist_le_dist_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk to itself and the center
  `c` of this disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`;

* `complex.abs_le_abs_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk with center `0` to itself,
  then for any point `z` of this disk we have `abs (f z) ≤ abs z`.

## Implementation notes

We prove some versions of the Schwarz lemma for a map `f : ℂ → E` taking values in any normed space
over complex numbers.

## TODO

* Prove that these inequalities are strict unless `f` is an affine map.

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open metric set function filter topological_space
open_locale topology

namespace complex

section space

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E}
  {c z z₀ : ℂ}

/-- An auxiliary lemma for `complex.norm_dslope_le_div_of_maps_to_ball`. -/
lemma schwarz_aux {f : ℂ → ℂ} (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  ‖dslope f c z‖ ≤ R₂ / R₁ :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  suffices : ∀ᶠ r in 𝓝[<] R₁, ‖dslope f c z‖ ≤ R₂ / r,
  { refine ge_of_tendsto _ this,
    exact (tendsto_const_nhds.div tendsto_id hR₁.ne').mono_left nhds_within_le_nhds },
  rw mem_ball at hz,
  filter_upwards [Ioo_mem_nhds_within_Iio ⟨hz, le_rfl⟩] with r hr,
  have hr₀ : 0 < r, from dist_nonneg.trans_lt hr.1,
  replace hd : diff_cont_on_cl ℂ (dslope f c) (ball c r),
  { refine differentiable_on.diff_cont_on_cl _,
    rw closure_ball c hr₀.ne',
    exact ((differentiable_on_dslope $ ball_mem_nhds _ hR₁).mpr hd).mono
      (closed_ball_subset_ball hr.2) },
  refine norm_le_of_forall_mem_frontier_norm_le bounded_ball hd _ _,
  { rw frontier_ball c hr₀.ne',
    intros z hz,
    have hz' : z ≠ c, from ne_of_mem_sphere hz hr₀.ne',
    rw [dslope_of_ne _ hz', slope_def_module, norm_smul, norm_inv, mem_sphere_iff_norm.1 hz,
      ← div_eq_inv_mul, div_le_div_right hr₀, ← dist_eq_norm],
    exact le_of_lt (h_maps (mem_ball.2 (by { rw mem_sphere.1 hz, exact hr.2 }))) },
  { rw [closure_ball c hr₀.ne', mem_closed_ball],
    exact hr.1.le }
end

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together. -/
lemma norm_dslope_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  ‖dslope f c z‖ ≤ R₂ / R₁ :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  have hR₂ : 0 < R₂, from nonempty_ball.1 ⟨f z, h_maps hz⟩,
  cases eq_or_ne (dslope f c z) 0 with hc hc,
  { rw [hc, norm_zero], exact div_nonneg hR₂.le hR₁.le },
  rcases exists_dual_vector ℂ _ hc with ⟨g, hg, hgf⟩,
  have hg' : ‖g‖₊ = 1, from nnreal.eq hg,
  have hg₀ : ‖g‖₊ ≠ 0, by simpa only [hg'] using one_ne_zero,
  calc ‖dslope f c z‖ = ‖dslope (g ∘ f) c z‖ :
    begin
      rw [g.dslope_comp, hgf, is_R_or_C.norm_of_real, norm_norm],
      exact λ _, hd.differentiable_at (ball_mem_nhds _ hR₁)
    end
  ... ≤ R₂ / R₁ :
    begin
      refine schwarz_aux (g.differentiable.comp_differentiable_on hd)
        (maps_to.comp _ h_maps) hz,
      simpa only [hg', nnreal.coe_one, one_mul] using g.lipschitz.maps_to_ball hg₀ (f c) R₂
    end
end

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_maps_to_ball`, if
`‖dslope f c z₀‖ = R₂ / R₁` holds at a point in the ball then the map `f` is affine. -/
lemma affine_of_maps_to_ball_of_exists_norm_dslope_eq_div [complete_space E]
  [strict_convex_space ℝ E] (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : set.maps_to f (ball c R₁) (ball (f c) R₂)) (h_z₀ : z₀ ∈ ball c R₁)
  (h_eq : ‖dslope f c z₀‖ = R₂ / R₁) :
  set.eq_on f (λ z, f c + (z - c) • dslope f c z₀) (ball c R₁) :=
begin
  set g := dslope f c,
  rintro z hz,
  by_cases z = c, { simp [h] },
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩,
  have g_le_div : ∀ z ∈ ball c R₁, ‖g z‖ ≤ R₂ / R₁,
    from λ z hz, norm_dslope_le_div_of_maps_to_ball hd h_maps hz,
  have g_max : is_max_on (norm ∘ g) (ball c R₁) z₀,
    from is_max_on_iff.mpr (λ z hz, by simpa [h_eq] using g_le_div z hz),
  have g_diff : differentiable_on ℂ g (ball c R₁),
    from (differentiable_on_dslope (is_open_ball.mem_nhds (mem_ball_self h_R₁))).mpr hd,
  have : g z = g z₀ := eq_on_of_is_preconnected_of_is_max_on_norm (convex_ball c R₁).is_preconnected
    is_open_ball g_diff h_z₀ g_max hz,
  simp [← this]
end

lemma affine_of_maps_to_ball_of_exists_norm_dslope_eq_div' [complete_space E]
  [strict_convex_space ℝ E] (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : set.maps_to f (ball c R₁) (ball (f c) R₂))
  (h_z₀ : ∃ z₀ ∈ ball c R₁, ‖dslope f c z₀‖ = R₂ / R₁) :
  ∃ C : E, ‖C‖ = R₂ / R₁ ∧ set.eq_on f (λ z, f c + (z - c) • C) (ball c R₁) :=
let ⟨z₀, h_z₀, h_eq⟩ := h_z₀ in
  ⟨dslope f c z₀, h_eq, affine_of_maps_to_ball_of_exists_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and a positive radius
`R₁` to an open ball with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
lemma norm_deriv_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) :
  ‖deriv f c‖ ≤ R₂ / R₁ :=
by simpa only [dslope_same] using norm_dslope_le_div_of_maps_to_ball hd h_maps (mem_ball_self h₀)

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and radius `R₁` to an
open ball with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
lemma dist_le_div_mul_dist_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  dist (f z) (f c) ≤ (R₂ / R₁) * dist z c :=
begin
  rcases eq_or_ne z c with rfl|hne, { simp only [dist_self, mul_zero] },
  simpa only [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv,
    ← div_eq_inv_mul, ← dist_eq_norm, div_le_iff (dist_pos.2 hne)]
    using norm_dslope_le_div_of_maps_to_ball hd h_maps hz
end

end space

variables {f : ℂ → ℂ} {c z : ℂ} {R R₁ R₂ : ℝ}

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `c` and a positive radius
`R₁` to an open disk with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
lemma abs_deriv_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) :
  abs (deriv f c) ≤ R₂ / R₁ :=
norm_deriv_le_div_of_maps_to_ball hd h_maps h₀

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk of positive radius to itself and the
center of this disk to itself, then the absolute value of the derivative of `f` at the center of
this disk is at most `1`. -/
lemma abs_deriv_le_one_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R))
  (h_maps : maps_to f (ball c R) (ball c R)) (hc : f c = c) (h₀ : 0 < R) :
  abs (deriv f c) ≤ 1 :=
(norm_deriv_le_div_of_maps_to_ball hd (by rwa hc) h₀).trans_eq (div_self h₀.ne')

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk to itself and the center `c` of this
disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`. -/
lemma dist_le_dist_of_maps_to_ball_self (hd : differentiable_on ℂ f (ball c R))
  (h_maps : maps_to f (ball c R) (ball c R)) (hc : f c = c) (hz : z ∈ ball c R) :
  dist (f z) c ≤ dist z c :=
have hR : 0 < R, from nonempty_ball.1 ⟨z, hz⟩,
by simpa only [hc, div_self hR.ne', one_mul]
  using dist_le_div_mul_dist_of_maps_to_ball hd (by rwa hc) hz

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `0` to itself, the for any
point `z` of this disk we have `abs (f z) ≤ abs z`. -/
lemma abs_le_abs_of_maps_to_ball_self (hd : differentiable_on ℂ f (ball 0 R))
  (h_maps : maps_to f (ball 0 R) (ball 0 R)) (h₀ : f 0 = 0) (hz : abs z < R) :
  abs (f z) ≤ abs z :=
begin
  replace hz : z ∈ ball (0 : ℂ) R, from mem_ball_zero_iff.2 hz,
  simpa only [dist_zero_right] using dist_le_dist_of_maps_to_ball_self hd h_maps h₀ hz
end

end complex

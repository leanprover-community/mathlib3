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

open asymptotics metric set function filter topological_space uniform_space.completion affine_map
open_locale topological_space

local postfix `̂`:100 := uniform_space.completion

namespace complex

variables {E F : Type*} [normed_add_comm_group E] [normed_space ℂ E] [normed_add_comm_group F]
  [normed_space ℂ F] {r R R₁ R₂ : ℝ} {n : ℕ}

lemma exists_differentiable_on_eq_zpow_succ_smul_add_of_is_o [complete_space E] {f : ℂ → E} {c : ℂ}
  {n : ℤ} (hd : differentiable_on ℂ f (ball c R₁))
  (ho : (λ x, f x - f c) =o[𝓝[≠] c] (λ x, (x - c) ^ n)) :
  ∃ (g : ℂ → E) y, differentiable_on ℂ g (ball c R₁) ∧ f = λ x, (x - c) ^ (n + 1) • g x + y :=
begin
  rcases eq_or_ne n (-1) with rfl|hn,
  { refine ⟨f, 0, hd, funext $ λ x, _⟩,
    rw [neg_add_self, zpow_zero, one_smul, add_zero] },
  have hn₀ : (0 : ℂ) ^ (n + 1) = 0,
    from zero_zpow _ (mt eq_neg_iff_add_eq_zero.2 hn),
  suffices : ∃ (g : ℂ → E), differentiable_on ℂ g (ball c R₁) ∧
    ∀ x ≠ c, (x - c) ^ (n + 1) • g x = f x - f c,
  { rcases this with ⟨g, hgd, hfg⟩,
    refine ⟨g, f c, hgd, funext $ λ x, _⟩,
    rcases eq_or_ne x c with rfl|hx,
    { rw [sub_self, hn₀, zero_smul, zero_add] },
    { rw [← sub_eq_iff_eq_add, ← hfg x hx] } },
  cases le_or_lt R₁ 0 with hR₁ hR₁,
  { rw [ball_eq_empty.2 hR₁],
    refine ⟨λ x, ((x - c) ^ (n + 1))⁻¹ • (f x - f c), differentiable_on_empty, λ x hx, _⟩,
    exact smul_inv_smul₀ (zpow_ne_zero _ (sub_ne_zero.2 hx)) _ },
  set g : ℂ → E := λ x, ((x - c) ^ (n + 1))⁻¹ • (f x - f c) with hg,
  have hgc : g c = 0,
  { simp only [g], rw [sub_self, hn₀, inv_zero, zero_smul] },
  refine ⟨update g c (lim (𝓝[≠] c) g), _, λ x hx, _⟩,
  { refine differentiable_on_update_lim_of_is_o (ball_mem_nhds _ hR₁) _ _,
    { simp only [g, ← zpow_neg],
      refine ((differentiable_on_id.sub_const c).zpow $ or.inl _).smul _,
      exacts [λ x hx, sub_ne_zero.2 hx.2, (hd.sub_const _).mono $ diff_subset _ _] },
    { calc (λ x, g x - g c) =ᶠ[𝓝[≠] c] g : by simp only [hgc, sub_zero]
      ... =o[𝓝[≠] c] λ x, ((x - c) ^ (n + 1))⁻¹ • (x - c) ^ n : _
      ... =ᶠ[𝓝[≠] c] λ x, (x - c)⁻¹ : _,
      { exact (is_O_refl (λ x, ((x - c) ^ (n + 1))⁻¹) (𝓝[≠] c)).smul_is_o ho },
      { refine eventually_mem_nhds_within.mono (λ x (hx : x ≠ c), _),
        simp only [smul_eq_mul, zpow_add_one₀ (sub_ne_zero.2 hx), mul_inv_rev],
        exact inv_mul_cancel_right₀ (zpow_ne_zero _ (sub_ne_zero.2 hx)) _ } } },
  { rw [update_noteq hx, smul_inv_smul₀],
    exact zpow_ne_zero _ (sub_ne_zero.2 hx) }
end

lemma exists_differentiable_on_eq_zpow_succ_smul_add_of_is_o₀ [complete_space E] {f : ℂ → E}
  {n : ℤ} (hd : differentiable_on ℂ f (ball 0 R₁))
  (ho : (λ x, f x - f 0) =o[𝓝[≠] (0 : ℂ)] (λ x, x ^ n)) :
  ∃ (g : ℂ → E) y, differentiable_on ℂ g (ball 0 R₁) ∧ f = λ x, x ^ (n + 1) • g x + y :=
have ho' : (λ x, f x - f 0) =o[𝓝[≠] (0 : ℂ)] (λ x, (x - 0) ^ n), by simpa only [sub_zero],
by simpa only [sub_zero] using exists_differentiable_on_eq_zpow_succ_smul_add_of_is_o hd ho'

lemma exists_differentiable_on_eq_pow_succ_smul_add_of_is_o [complete_space E] {f : ℂ → E} {c : ℂ}
  {n : ℕ} (hd : differentiable_on ℂ f (ball c R₁))
  (ho : (λ x, f x - f c) =o[𝓝[≠] c] (λ x, (x - c) ^ n)) :
  ∃ (g : ℂ → E) y, differentiable_on ℂ g (ball c R₁) ∧ f = λ x, (x - c) ^ (n + 1) • g x + y :=
begin
  simp only [← zpow_coe_nat, nat.cast_succ] at *,
  exact exists_differentiable_on_eq_zpow_succ_smul_add_of_is_o hd ho
end

lemma exists_differentiable_on_eq_pow_succ_smul_add_of_is_o₀ [complete_space E] {f : ℂ → E}
  {n : ℕ} (hd : differentiable_on ℂ f (ball 0 R₁))
  (ho : (λ x, f x - f 0) =o[𝓝[≠] (0 : ℂ)] (λ x, x ^ n)) :
  ∃ (g : ℂ → E) y, differentiable_on ℂ g (ball 0 R₁) ∧ f = λ x, x ^ (n + 1) • g x + y :=
have ho' : (λ x, f x - f 0) =o[𝓝[≠] (0 : ℂ)] (λ x, (x - 0) ^ n), by simpa only [sub_zero],
by simpa only [sub_zero] using exists_differentiable_on_eq_pow_succ_smul_add_of_is_o hd ho'

lemma schwarz_aux₁ [complete_space E] {f : ℂ → E} {c z : ℂ} (hd : differentiable_on ℂ f (ball c R₁))
  (hnorm : ∀ z ∈ ball c R₁, ∥(z - c) ^ (n + 1) • f z∥ ≤ R₂) (hz : z ∈ ball c R₁) :
  ∥f z∥ ≤ R₂ / R₁ ^ (n + 1) :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  suffices : ∀ᶠ r in 𝓝[<] R₁, ∥f z∥ ≤ R₂ / r ^ (n + 1),
  { refine ge_of_tendsto _ this,
    exact tendsto_const_nhds.div ((tendsto_id.mono_left nhds_within_le_nhds).pow _)
      (pow_ne_zero _ hR₁.ne') },
  rw [mem_ball] at hz,
  filter_upwards [Ioo_mem_nhds_within_Iio ⟨hz, le_rfl⟩] with r hr,
  have hdr : diff_cont_on_cl ℂ f (ball c r),
  { refine (hd.mono _).diff_cont_on_cl,
    exact closure_ball_subset_closed_ball.trans (closed_ball_subset_ball hr.2) },
  refine norm_le_of_forall_mem_sphere_norm_le hdr (λ w hw, _) hr.1.le,
  have hr₀ : 0 < r, from dist_nonneg.trans_lt hr.1,
  rw [le_div_iff' (pow_pos hr₀ _), ← (mem_sphere_iff_norm _ _ _).mp hw, ← norm_pow, ← norm_smul],
  exact hnorm _ (sphere_subset_ball hr.2 hw)
end


lemma dist_le_of_maps_to_ball_of_is_o {f : E → F} {c z : E} (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂))
  (ho : (λ x, f x - f c) =o[𝓝[≠] c] (λ x, ∥x - c∥ ^ n)) (hz : z ∈ ball c R₁) :
  dist (f z) (f c) ≤ (dist z c / R₁) ^ (n + 1) * R₂ :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  rcases eq_or_ne z c with rfl|hne, { simp },
  set f₁ : ℂ → F̂ := λ ζ, f (line_map c z ζ) with hf₁,
  suffices H : dist (f₁ 1) (f₁ 0) ≤ R₂ / (R₁ / dist z c) ^ (n + 1),
  { simp only [hf₁] at H,
    rwa [line_map_apply_zero, line_map_apply_one, uniform_space.completion.dist_eq,
      div_eq_inv_mul R₂, ← inv_pow, inv_div] at H },
  replace ho : (λ ζ : ℂ, f₁ ζ - f₁ 0) =o[𝓝[≠] (0 : ℂ)] (λ ζ, ζ ^ n),
  { simp_rw [hf₁, ← uniform_space.completion.coe_sub, is_o_completion_left, line_map_apply_zero],
    refine ((ho.comp_tendsto _).congr_right $ λ x, _).of_norm_right,
    { refine (line_map_continuous.tendsto' _ _ (line_map_apply_zero _ _)).inf _,
      simp },
    { sorry } },
end
  

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and radius `R₁` to an
open ball with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
lemma dist_le_div_mul_dist_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  dist (f z) (f c) ≤ (R₂ / R₁) * dist z c :=
begin
end


/-- An auxiliary lemma for `complex.norm_dslope_le_div_of_maps_to_ball`. -/
lemma schwarz_aux {f : ℂ → E} {c z : ℂ} (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) (hne : z ≠ c)
  (ho : (λ x, f x - f c) =o[𝓝[≠] c] (λ x, (x - c) ^ n)) :
  dist (f z) (f c) ≤ (dist z c / R₁) ^ (n + 1) * R₂ ∧
    dist (f z) (f c) = (dist z c / R₁) ^ (n + 1) * R₂ →
      (∀ w ∈ ball c R₁, dist (f w) (f c) = (dist w c / R₁) ^ (n + 1) * R₂) ∧
      (strict_convex_space ℝ E →
        ∀ w ∈ ball c R₁, f w = ((w - c) / (z - c)) ^ (n + 1) • (f z - f c) + f c) :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  obtain ⟨g, y, hgd, hgf⟩ :=
    exists_differentiable_on_eq_pow_succ_smul_add_of_is_o hd.coe_completion (by exact_mod_cast ho),
  replace hgf : ∀ w, (f w - f c : Ê) = (w - c) ^ (n + 1) • g w,
  { intro w, have := congr_fun hgf, dsimp only at this, simp [this] },
  simp only [maps_to, mem_ball, dist_eq_norm, dist_eq, ← @norm_coe E, coe_sub, hgf] at h_maps ⊢,

  -- have : 
  -- suffices : ∀ᶠ r in 𝓝[<] R₁, dist (f z) (f c) ≤ (dist z c / r) ^ (n + 1) * R₂,
  -- { refine ge_of_tendsto _ this,
  --   exact (((tendsto_const_nhds.div tendsto_id hR₁.ne').pow _).mul_const _).mono_left
  --     nhds_within_le_nhds },
  -- clear hd ho,
  -- rw mem_ball at hz,
  -- filter_upwards [Ioo_mem_nhds_within_Iio ⟨hz, le_rfl⟩] with r hr,
  -- simp only [sub_self, zero_pow n.succ_pos, zero_smul, zero_add, dist_eq_norm, add_sub_cancel,
  --   norm_smul, norm_pow, div_pow, div_mul_comm _ _ R₂] at h_maps ⊢, rw mul_comm,
  -- refine mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _),
  
  -- have hr₀ : 0 < r, from dist_nonneg.trans_lt hr.1,
  -- have hr₀' : r ≠ 0, from hr₀.ne',
  -- have hbr : closed_ball c r ⊆ ball c R₁, from closed_ball_subset_ball hr.2,
  -- set g : ℂ → E := λ x, ((x - c) ^ (n + 1))⁻¹ • (f x - f c) with hg,
  -- set G : ℂ → E := update g c (lim (𝓝[≠] c) g) with hG,
  -- have hGn : ∀ {x C}, x ≠ c → (∥G x∥ ≤ C ↔ dist (f x) (f c) ≤ C * (dist x c) ^ (n + 1)),
  -- { intros x C hx,
  --   rw [hG, update_noteq hx, hg, norm_smul, norm_inv, norm_pow, ← div_eq_inv_mul, ← dist_eq_norm,
  --     ← dist_eq_norm, div_le_iff (pow_pos (dist_pos.2 hx) _)] },
  -- suffices : ∥G z∥ ≤ R₂ / r ^ (n + 1),
  -- { rwa [hGn hne, div_mul_comm, ← div_pow] at this },
  -- have hgc : g c = 0, by simp_rw [hg, sub_self (f c), smul_zero],
  -- have hgd : differentiable_on ℂ g (closed_ball c r \ {c}),
  -- { refine differentiable_on.smul _ ((hd.mono $ (diff_subset _ _).trans hbr).sub_const _),
  --   refine ((differentiable_on_id.sub_const _).pow _).inv (λ x hx, pow_ne_zero _ _),
  --   exact sub_ne_zero.2 hx.2 },
  -- have hgo : (λ z, g z - g c) =o[𝓝[≠] c] λ z, (z - c)⁻¹,
  -- { calc (λ x, g x - g c) =ᶠ[𝓝[≠] c] g : by simp only [hgc, sub_zero]
  --   ... =o[𝓝[≠] c] λ x, ((x - c) ^ (n + 1))⁻¹ • (x - c) ^ n : (is_O_refl _ _).smul_is_o ho
  --   ... =ᶠ[𝓝[≠] c] λ x, (x - c)⁻¹ : eventually_mem_nhds_within.mono $ λ x (hx : x ≠ c),
  --     by simp only [smul_eq_mul, pow_succ, mul_inv,
  --       inv_mul_cancel_right₀ (pow_ne_zero _ (sub_ne_zero.2 hx))] },
  -- have hGd : diff_cont_on_cl ℂ G (ball c r),
  -- { apply differentiable_on.diff_cont_on_cl,
  --   rw [closure_ball c hr₀'],
  --   exact differentiable_on_update_lim_of_is_o (closed_ball_mem_nhds _ hr₀) hgd hgo },
  -- refine norm_le_of_forall_mem_frontier_norm_le bounded_ball hGd _ (subset_closure hr.1),
  -- rw frontier_ball c hr₀',
  -- intros z hz,
  -- rw [hGn (ne_of_mem_sphere hz hr₀'), mem_sphere.1 hz, div_mul_cancel _ (pow_ne_zero _ hr₀')],
  -- exact le_of_lt (h_maps $ hbr $ le_of_eq hz)
end

lemma dist_le_div_pow_succ_mul_of_maps_to_ball_of_is_o {f : E → F} {c z : E}
  (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁)
  (ho : (λ x, f x - f c) =o[𝓝 c] (λ x, ∥x - c∥ ^ n)) :
  dist (f z) (f c) ≤ (dist z c / R₁) ^ (n + 1) * R₂ :=
begin
end

/-- The **Schwarz Lemma**: if `f : E → F` sends an open disk with center `c` and radius `R₁` to an
open ball with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
lemma dist_le_div_mul_dist_of_maps_to_ball {f : E → F} {c z : E}
  (hd : differentiable_on ℂ f (ball c R₁)) (h_maps : maps_to f (ball c R₁) (ball (f c) R₂))
  (hz : z ∈ ball c R₁) :
  dist (f z) (f c) ≤ (R₂ / R₁) * dist z c :=
begin
  
end

#exit

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together. -/
lemma norm_dslope_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  ∥dslope f c z∥ ≤ R₂ / R₁ :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  have hR₂ : 0 < R₂, from nonempty_ball.1 ⟨f z, h_maps hz⟩,
  cases eq_or_ne (dslope f c z) 0 with hc hc,
  { rw [hc, norm_zero], exact div_nonneg hR₂.le hR₁.le },
  rcases exists_dual_vector ℂ _ hc with ⟨g, hg, hgf⟩,
  have hg' : ∥g∥₊ = 1, from nnreal.eq hg,
  have hg₀ : ∥g∥₊ ≠ 0, by simpa only [hg'] using one_ne_zero,
  calc ∥dslope f c z∥ = ∥dslope (g ∘ f) c z∥ :
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

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and a positive radius
`R₁` to an open ball with center `f c` and radius `R₂`, then the norm of the derivative of `f` at
`c` is at most the ratio `R₂ / R₁`. -/
lemma norm_deriv_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) :
  ∥deriv f c∥ ≤ R₂ / R₁ :=
by simpa only [dslope_same] using norm_dslope_le_div_of_maps_to_ball hd h_maps (mem_ball_self h₀)

end space

section space_space

variables {E F : Type*} [normed_group E] [normed_space ℂ E] [normed_group F] [normed_space ℂ F]
  {R R₁ R₂ : ℝ} {f : E → F} {c z : E}

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and radius `R₁` to an
open ball with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
lemma dist_le_div_mul_dist_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  dist (f z) (f c) ≤ (R₂ / R₁) * dist z c :=
begin
  rcases eq_or_ne z c with rfl|hne, { simp only [dist_self, mul_zero] },
  have h₀ : ∥z - c∥ ≠ 0, by simpa [sub_eq_zero],
  obtain ⟨x, y, hx₀, hx, hy, rfl⟩ : ∃ (x : ℝ) (y : E), 0 ≤ x ∧ x < R₁ ∧ ∥y∥ = 1 ∧ c + x • y = z,
  { refine ⟨∥z - c∥, (∥z - c∥)⁻¹ • (z - c), norm_nonneg _, mem_ball_iff_norm.1 hz, _, _⟩,
    { rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel h₀] },
    { rw [smul_inv_smul₀ h₀, add_sub_cancel'_right] } },
  set g : ℂ → F := λ a, f (c + a • y),
  
-- simpa only [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv,
  --   ← div_eq_inv_mul, ← dist_eq_norm, div_le_iff (dist_pos.2 hne)]
  --   using norm_dslope_le_div_of_maps_to_ball hd h_maps hz
end

/-- The **Schwarz Lemma**: if `f : E → F` sends an open disk with center `c` and a positive radius
`R₁` to an open ball with center `f c` and radius `R₂`, then the norm of the Fréchet derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
lemma norm_fderiv_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) :
  ∥fderiv ℝ f c∥ ≤ R₂ / R₁ :=
have hR₂ : 0 < R₂, from nonempty_ball.1 ⟨f c, h_maps $ mem_ball_self h₀⟩,
continuous_linear_map.op_norm_le_of_unit_norm (div_pos hR₂ h₀).le $ λ z hz,
calc ∥fderiv ℝ f c z∥ = ∥deriv (λ x : ℂ, f (c + x • z)) 0∥ : _
... ≤ R₂ / R₁ : norm_deriv_le_div_of_maps_to_ball

end space_space

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

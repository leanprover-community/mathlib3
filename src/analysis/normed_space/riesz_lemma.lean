/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import topology.metric_space.hausdorff_distance

/-!
# Riesz's lemma

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace `F` of `E`, there is a nonzero `x` such that `∥x - F∥`
is at least `r * ∥x∥` for any `r < 1`. This is `riesz_lemma`.

In a nondiscrete normed field (with an element `c` of norm `> 1`) and any `R > ∥c∥`, one can
guarantee `∥x∥ ≤ R` and `∥x - y∥ ≥ 1` for any `y` in `F`. This is `riesz_lemma_of_norm_lt`.
-/

variables {𝕜 : Type*} [normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. For a variant giving an element with norm in `[1, R]`, see
`riesz_lemma_of_norm_lt`. -/
lemma riesz_lemma {F : subspace 𝕜 E} (hFc : is_closed (F : set E))
  (hF : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
  ∃ x₀ : E, x₀ ∉ F ∧ ∀ y ∈ F, r * ∥x₀∥ ≤ ∥x₀ - y∥ :=
begin
  classical,
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ F := hF,
  let d := metric.inf_dist x F,
  have hFn : (F : set E).nonempty, from ⟨_, F.zero_mem⟩,
  have hdp : 0 < d,
    from lt_of_le_of_ne metric.inf_dist_nonneg (λ heq, hx
    ((metric.mem_iff_inf_dist_zero_of_closed hFc hFn).2 heq.symm)),
  let r' := max r 2⁻¹,
  have hr' : r' < 1, by { simp [r', hr], norm_num },
  have hlt : 0 < r' := lt_of_lt_of_le (by norm_num) (le_max_right r 2⁻¹),
  have hdlt : d < d / r', from (lt_div_iff hlt).mpr ((mul_lt_iff_lt_one_right hdp).2 hr'),
  obtain ⟨y₀, hy₀F, hxy₀⟩ : ∃ y ∈ F, dist x y < d / r' :=
    metric.exists_dist_lt_of_inf_dist_lt hdlt hFn,
  have x_ne_y₀ : x - y₀ ∉ F,
  { by_contradiction h,
    have : (x - y₀) + y₀ ∈ F, from F.add_mem h hy₀F,
    simp only [neg_add_cancel_right, sub_eq_add_neg] at this,
    exact hx this },
  refine ⟨x - y₀, x_ne_y₀, λy hy, le_of_lt _⟩,
  have hy₀y : y₀ + y ∈ F, from F.add_mem hy₀F hy,
  calc
    r * ∥x - y₀∥ ≤ r' * ∥x - y₀∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    ... < d : by { rw ←dist_eq_norm, exact (lt_div_iff' hlt).1 hxy₀ }
    ... ≤ dist x (y₀ + y) : metric.inf_dist_le_dist_of_mem hy₀y
    ... = ∥x - y₀ - y∥ : by { rw [sub_sub, dist_eq_norm] }
end

/--
A version of Riesz lemma: given a strict closed subspace `F`, one may find an element of norm `≤ R`
which is at distance  at least `1` of every element of `F`. Here, `R` is any given constant
strictly larger than the norm of an element of norm `> 1`. For a version without an `R`, see
`riesz_lemma`.

Since we are considering a general nondiscrete normed field, there may be a gap in possible norms
(for instance no element of norm in `(1,2)`). Hence, we can not allow `R` arbitrarily close to `1`,
and require `R > ∥c∥` for some `c : 𝕜` with norm `> 1`.
-/
lemma riesz_lemma_of_norm_lt
  {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R)
  {F : subspace 𝕜 E} (hFc : is_closed (F : set E)) (hF : ∃ x : E, x ∉ F) :
  ∃ x₀ : E, ∥x₀∥ ≤ R ∧ ∀ y ∈ F, 1 ≤ ∥x₀ - y∥ :=
begin
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR,
  have : ∥c∥ / R < 1, by { rw div_lt_iff Rpos, simpa using hR },
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩,
  have x0 : x ≠ 0 := λ H, by simpa [H] using xF,
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    ∃ (d : 𝕜), d ≠ 0 ∧ ∥d • x∥ < R ∧ R / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ R⁻¹ * ∥c∥ * ∥x∥ :=
      rescale_to_shell hc Rpos x0,
  refine ⟨d • x, dxlt.le, λ y hy, _⟩,
  set y' := d⁻¹ • y with hy',
  have y'F : y' ∈ F, by simp [hy', submodule.smul_mem _ _ hy],
  have yy' : y = d • y', by simp [hy', smul_smul, mul_inv_cancel d0],
  calc 1 = (∥c∥/R) * (R/∥c∥) : by field_simp [Rpos.ne', (zero_lt_one.trans hc).ne']
  ... ≤ (∥c∥/R) * (∥d • x∥) :
    mul_le_mul_of_nonneg_left ledx (div_nonneg (norm_nonneg _) Rpos.le)
  ... = ∥d∥ * (∥c∥/R * ∥x∥) : by { simp [norm_smul], ring }
  ... ≤ ∥d∥ * ∥x - y'∥ :
    mul_le_mul_of_nonneg_left (hx y' (by simp [hy', submodule.smul_mem _ _ hy])) (norm_nonneg _)
  ... = ∥d • x - y∥ : by simp [yy', ← smul_sub, norm_smul],
end

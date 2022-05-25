/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.calculus.dslope
import analysis.calculus.fderiv_analytic
import analysis.complex.basic

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `formal_multilinear_series` namespace that
is specific to this setup.

## Main definitions

When `p` is a formal multilinear series from `𝕜` to `E`:
* `p.coef n` is the `n`th coefficient of `p` seen as a power series in `𝕜`, which is equal to `p n
  (λ i : fin n, 1)`;
* `p.order` (taking values in `with_top ℕ`) is the index of the first non-zero coefficient of the
  series, or `⊤` it `p n` is identically `0`. This is the order of the zero of an analytic function
  `f` at a point if `p` is the Taylor series of `f` at that point;
* `p.fslope` is the series obtained by dropping the term of order `0` and dividing by the parameter,
  corresponding to the Taylor series of `dslope f` if `p` is the Taylor series of `f`.

## Main results

* `has_fpower_series_at_iff` states that `has_fpower_series_at f p z₀` is equivalent to `f` being
  locally the sum of `p`, in the sense that `∀ᶠ z in 𝓝 0, has_sum (λ n, p n (λ _, z)) (f (z₀ + z))`
  (this version is easier to work with in some setups).
* `analytic_at.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if an analytic
  function is `0` at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it has
  no other zero in a neighborhood of `z₀`.
-/

open filter function nat
open_locale topological_space big_operators

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {s : E}
  {p : formal_multilinear_series 𝕜 𝕜 E} {f : 𝕜 → E}
  {n : ℕ} {z z₀ : 𝕜} {y : fin n → 𝕜}

namespace formal_multilinear_series

/-- The `n`th coefficient of `p` when seen as a power series. -/
def coef (p : formal_multilinear_series 𝕜 𝕜 E) (n : ℕ) : E := p n 1

@[simp] lemma apply_eq_prod_smul_coef : p n y = (∏ i, y i) • p.coef n :=
begin
  convert (p n).to_multilinear_map.map_smul_univ y 1,
  funext; simp only [pi.one_apply, algebra.id.smul_eq_mul, mul_one],
end

@[simp] lemma apply_eq_pow_smul_coef : p n (λ _, z) = z ^ n • coef p n :=
by simp

@[simp] lemma norm_eq_norm_coef : ∥p n∥ = ∥coef p n∥ :=
begin
  apply le_antisymm,
  { refine (p n).op_norm_le_bound (norm_nonneg (coef p n)) (λ y, _); simp [norm_smul, mul_comm] },
  { apply le_of_le_of_eq ((p n).le_op_norm 1); simp }
end

/-- The index of the first non-zero coefficient in `p`. -/
noncomputable def order (p : formal_multilinear_series 𝕜 𝕜 E) : with_top ℕ :=
by classical; exact dite (∀ n, p.coef n = 0) (λ _, ⊤) (λ h, nat.find (not_forall.mp h))

lemma order_eq_zero_iff : p.order = 0 ↔ p.coef 0 ≠ 0 :=
by { by_cases (∀ n, coef p n = 0); simp [order, h] }

lemma order_eq_top_iff : p.order = ⊤ ↔ ∀ n, p.coef n = 0 :=
by { by_cases (∀ n, coef p n = 0); simp [order, h] }

/-- The formal counterpart of `dslope`, corresponding to the expansion of `(f z - f 0) / z`. If `f`
has `p` as a power series, then `dslope f` has `fslope p` as a power series. -/
noncomputable def fslope (p : formal_multilinear_series 𝕜 𝕜 E) : formal_multilinear_series 𝕜 𝕜 E :=
  λ n, (p (n + 1)).curry_left 1

@[simp] lemma coef_fslope (n : ℕ) :
  p.fslope.coef n = p.coef (n + 1) :=
begin
  have : @fin.cons n (λ _, 𝕜) 1 (1 : fin n → 𝕜) = 1 := fin.cons_self_tail 1,
  simp only [fslope, coef, continuous_multilinear_map.curry_left_apply, this],
end

@[simp] lemma order_fslope (ho : p.coef 0 = 0) : p.fslope.order = p.order - 1 :=
begin
  suffices : p.order = p.fslope.order + 1,
  { by_cases (p.fslope.order = ⊤); { rw [this, h] <|> rw [this, ←with_top.coe_untop _ h], refl } },
  by_cases (∀ n, p.coef n = 0),
  { have h1 : ∀ n, p.fslope.coef n = 0 := by simp only [h, coef_fslope, forall_const],
    simp only [order, h, h1, forall_const, dif_pos, with_top.top_add] },
  { have h2 : ¬∀ n, p.coef (n + 1) = 0 := λ hn, h (λ n, nat.cases_on n ho hn),
    simp only [order, h, h2, not_false_iff, coef_fslope, dif_neg],
    norm_cast,
    exact find_comp_succ _ _ (not_not.mpr ho) }
end

end formal_multilinear_series

namespace has_fpower_series_at

open formal_multilinear_series emetric

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`has_fpower_series_at` depends on `p.radius`. -/
lemma _root_.has_fpower_series_at_iff : has_fpower_series_at f p z₀ ↔
  ∀ᶠ z in 𝓝 0, has_sum (λ n, p n (λ _, z)) (f (z₀ + z)) :=
begin
  refine ⟨λ ⟨r, r_le, r_pos, h⟩, eventually_of_mem (ball_mem_nhds 0 r_pos) (λ _, h), _⟩,
  simp only [metric.eventually_nhds_iff],
  rintro ⟨r, r_pos, h⟩,
  refine ⟨p.radius ⊓ r.to_nnreal, by simp, _, _⟩,
  { simp only [r_pos.lt, lt_inf_iff, ennreal.coe_pos, real.to_nnreal_pos, and_true],
    obtain ⟨z, z_pos, le_z⟩ := normed_field.exists_norm_lt 𝕜 r_pos.lt,
    have : (∥z∥₊ : ennreal) ≤ p.radius := by {
      simp only [dist_zero_right] at h,
      apply formal_multilinear_series.le_radius_of_tendsto,
      convert tendsto_norm.comp (h le_z).summable.tendsto_at_top_zero,
      funext; simp [norm_smul, mul_comm] },
    refine lt_of_lt_of_le _ this,
    simp only [ennreal.coe_pos],
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos)) },
  { simp only [mem_ball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coef, and_imp, dist_zero_right] at h ⊢,
    refine λ y hyp hyr, h _,
    simpa [nndist_eq_nnnorm, real.lt_to_nnreal_iff_coe_lt] using hyr }
end

lemma locally_zero_of_order_eq_top' (hp : has_fpower_series_at f p z₀) (h : p.order = ⊤) :
  ∀ᶠ z in 𝓝 0, f (z₀ + z) = 0 :=
begin
  simp only [has_fpower_series_at_iff, order_eq_top_iff.mp h, apply_eq_pow_smul_coef, smul_zero] at hp,
  exact hp.mono (λ x hx, has_sum.unique hx has_sum_zero)
end

lemma locally_zero_of_order_eq_top (hp : has_fpower_series_at f p z₀) (h : p.order = ⊤) :
  ∀ᶠ z in 𝓝 z₀, f z = 0 :=
begin
  have : tendsto (λ z, z - z₀) (𝓝 z₀) (𝓝 0) := sub_self z₀ ▸ filter.tendsto_id.sub_const z₀,
  simpa using this.eventually (locally_zero_of_order_eq_top' hp h),
end

lemma has_fpower_series_dslope_fslope (hp : has_fpower_series_at f p z₀) :
  has_fpower_series_at (dslope f z₀) p.fslope z₀ :=
begin
  have hpd : deriv f z₀ = p.coef 1 := hp.deriv,
  have hp0 : p.coef 0 = f z₀ := hp.coeff_zero 1,
  simp only [has_fpower_series_at_iff, apply_eq_pow_smul_coef, coef_fslope] at hp ⊢,
  refine hp.mono (λ x hx, _),
  by_cases x = 0,
  { convert has_sum_single 0 _; intros; simp [*] },
  { have hxx : ∀ (n : ℕ), x⁻¹ * x ^ (n + 1) = x ^ n := λ n, by field_simp [h, pow_succ'],
    suffices : has_sum (λ n, x⁻¹ • x ^ (n + 1) • p.coef (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)),
    { simpa [dslope, slope, h, smul_smul, hxx] using this },
    { simpa [hp0] using ((has_sum_nat_add_iff' 1).mpr hx).const_smul } }
end

lemma locally_ne_zero_aux (hp : has_fpower_series_at f p z₀) {n : ℕ} (h : p.order = n) :
  ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
begin
  induction n with n ih generalizing f p,
  { apply eventually_nhds_within_of_eventually_nhds,
    refine hp.continuous_at.eventually (is_open_compl_singleton.eventually_mem _),
    simpa [← hp.coeff_zero 1, order_eq_zero_iff] using h },
  { have hp0 : p.coef 0 = f z₀ := hp.coeff_zero 1,
    have order_ne_0 : p.order ≠ 0 := by { by_contra h'; rw h' at h; norm_cast at h },
    have hf0 : f z₀ = 0 :=
      by simpa [← hp0, order_eq_zero_iff.not] using order_ne_0,
    have ofslope : p.fslope.order = n := by {
      rw [order_fslope (hp0.symm ▸ hf0 : p.coef 0 = 0), h]; norm_cast },
    simp only [eventually_nhds_within_iff] at ih ⊢,
    refine (ih hp.has_fpower_series_dslope_fslope ofslope).mono (λ z hs hz hf, _),
    specialize hs hz,
    change z ≠ z₀ at hz,
    simp [dslope, hz, slope, sub_eq_zero, hf0] at hs,
    exact hs hf },
end

end has_fpower_series_at

namespace analytic_at

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : analytic_at 𝕜 f z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) :=
begin
  rcases hf with ⟨p, hp⟩,
  by_cases (p.order = ⊤),
  { simpa using or.inl (hp.locally_zero_of_order_eq_top h) },
  { let o := with_top.untop _ h,
    have : p.order = o := by simp only [with_top.coe_untop],
    exact or.inr (hp.locally_ne_zero_aux this) }
end

end analytic_at

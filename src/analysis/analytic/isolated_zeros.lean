/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.analytic.basic
import analysis.calculus.dslope
import analysis.calculus.fderiv_analytic
import analysis.calculus.formal_multilinear_series
import analysis.analytic.uniqueness

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `has_fpower_series_at` namespace that is
useful in this setup.

## Main results

* `analytic_at.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `analytic_on.eq_on_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.
-/

open_locale classical

open filter function nat formal_multilinear_series emetric set
open_locale topology big_operators

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {s : E}
  {p q : formal_multilinear_series 𝕜 𝕜 E} {f g : 𝕜 → E}
  {n : ℕ} {z z₀ : 𝕜} {y : fin n → 𝕜}

namespace has_sum

variables {a : ℕ → E}

lemma has_sum_at_zero (a : ℕ → E) : has_sum (λ n, (0:𝕜) ^ n • a n) (a 0) :=
by convert has_sum_single 0 (λ b h, _); simp [nat.pos_of_ne_zero h] <|> simp

lemma exists_has_sum_smul_of_apply_eq_zero (hs : has_sum (λ m, z ^ m • a m) s)
  (ha : ∀ k < n, a k = 0) :
  ∃ t : E, z ^ n • t = s ∧ has_sum (λ m, z ^ m • a (m + n)) t :=
begin
  obtain rfl | hn := n.eq_zero_or_pos,
  { simpa },
  by_cases h : z = 0,
  { have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using has_sum_at_zero a),
    exact ⟨a n, by simp [h, hn, this], by simpa [h] using has_sum_at_zero (λ m, a (m + n))⟩ },
  { refine ⟨(z ^ n)⁻¹ • s, by field_simp [smul_smul], _⟩,
    have h1 : ∑ i in finset.range n, z ^ i • a i = 0,
      from finset.sum_eq_zero (λ k hk, by simp [ha k (finset.mem_range.mp hk)]),
    have h2 : has_sum (λ m, z ^ (m + n) • a (m + n)) s,
      by simpa [h1] using (has_sum_nat_add_iff' n).mpr hs,
    convert h2.const_smul (z⁻¹ ^ n),
    { field_simp [pow_add, smul_smul] },
    { simp only [inv_pow] } }
end

end has_sum

namespace has_fpower_series_at

lemma has_fpower_series_dslope_fslope (hp : has_fpower_series_at f p z₀) :
  has_fpower_series_at (dslope f z₀) p.fslope z₀ :=
begin
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv,
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1,
  simp only [has_fpower_series_at_iff, apply_eq_pow_smul_coeff, coeff_fslope] at hp ⊢,
  refine hp.mono (λ x hx, _),
  by_cases h : x = 0,
  { convert has_sum_single 0 _; intros; simp [*] },
  { have hxx : ∀ (n : ℕ), x⁻¹ * x ^ (n + 1) = x ^ n := λ n, by field_simp [h, pow_succ'],
    suffices : has_sum (λ n, x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)),
    { simpa [dslope, slope, h, smul_smul, hxx] using this },
    { simpa [hp0] using ((has_sum_nat_add_iff' 1).mpr hx).const_smul x⁻¹ } }
end

lemma has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : has_fpower_series_at f p z₀) :
  has_fpower_series_at ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ :=
begin
  induction n with n ih generalizing f p,
  { exact hp },
  { simpa using ih (has_fpower_series_dslope_fslope hp) }
end

lemma iterate_dslope_fslope_ne_zero (hp : has_fpower_series_at f p z₀) (h : p ≠ 0) :
  (swap dslope z₀)^[p.order] f z₀ ≠ 0 :=
begin
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1],
  simpa [coeff_eq_zero] using apply_order_ne_zero h
end

lemma eq_pow_order_mul_iterate_dslope (hp : has_fpower_series_at f p z₀) :
  ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ p.order • ((swap dslope z₀)^[p.order] f z) :=
begin
  have hq := has_fpower_series_at_iff'.mp (has_fpower_series_iterate_dslope_fslope p.order hp),
  filter_upwards [hq, has_fpower_series_at_iff'.mp hp] with x hx1 hx2,
  have : ∀ k < p.order, p.coeff k = 0,
    from λ k hk, by simpa [coeff_eq_zero] using apply_eq_zero_of_lt_order hk,
  obtain ⟨s, hs1, hs2⟩ := has_sum.exists_has_sum_smul_of_apply_eq_zero hx2 this,
  convert hs1.symm,
  simp only [coeff_iterate_fslope] at hx1,
  exact hx1.unique hs2
end

lemma locally_ne_zero (hp : has_fpower_series_at f p z₀) (h : p ≠ 0) :
  ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
begin
  rw [eventually_nhds_within_iff],
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuous_at,
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h),
  filter_upwards [eq_pow_order_mul_iterate_dslope hp, h3] with z e1 e2 e3,
  simpa [e1, e2, e3] using pow_ne_zero p.order (sub_ne_zero.mpr e3),
end

lemma locally_zero_iff (hp : has_fpower_series_at f p z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
⟨λ hf, hp.eq_zero_of_eventually hf, λ h, eventually_eq_zero (by rwa h at hp)⟩

end has_fpower_series_at

namespace analytic_at

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : analytic_at 𝕜 f z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) :=
begin
  rcases hf with ⟨p, hp⟩,
  by_cases h : p = 0,
  { exact or.inl (has_fpower_series_at.eventually_eq_zero (by rwa h at hp)) },
  { exact or.inr (hp.locally_ne_zero h) }
end

lemma eventually_eq_or_eventually_ne (hf : analytic_at 𝕜 f z₀) (hg : analytic_at 𝕜 g z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = g z) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ g z) :=
by simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero

lemma frequently_zero_iff_eventually_zero {f : 𝕜 → E} {w : 𝕜} (hf : analytic_at 𝕜 f w) :
  (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ (∀ᶠ z in 𝓝 w, f z = 0) :=
⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right,
  λ h, (h.filter_mono nhds_within_le_nhds).frequently⟩

lemma frequently_eq_iff_eventually_eq (hf : analytic_at 𝕜 f z₀) (hg : analytic_at 𝕜 g z₀) :
  (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ (∀ᶠ z in 𝓝 z₀, f z = g z) :=
by simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

end analytic_at

namespace analytic_on

variables {U : set 𝕜}

/-- The *principle of isolated zeros* for an analytic function, global version: if a function is
analytic on a connected set `U` and vanishes in arbitrary neighborhoods of a point `z₀ ∈ U`, then
it is identically zero in `U`.
For higher-dimensional versions requiring that the function vanishes in a neighborhood of `z₀`,
see `eq_on_zero_of_preconnected_of_eventually_eq_zero`. -/
theorem eq_on_zero_of_preconnected_of_frequently_eq_zero
  (hf : analytic_on 𝕜 f U) (hU : is_preconnected U)
  (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) :
  eq_on f 0 U :=
hf.eq_on_zero_of_preconnected_of_eventually_eq_zero hU h₀
  ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)

theorem eq_on_zero_of_preconnected_of_mem_closure (hf : analytic_on 𝕜 f U) (hU : is_preconnected U)
  (h₀ : z₀ ∈ U) (hfz₀ : z₀ ∈ closure ({z | f z = 0} \ {z₀})) :
  eq_on f 0 U :=
hf.eq_on_zero_of_preconnected_of_frequently_eq_zero hU h₀
  (mem_closure_ne_iff_frequently_within.mp hfz₀)

/-- The *identity principle* for analytic functions, global version: if two functions are
analytic on a connected set `U` and coincide at points which accumulate to a point `z₀ ∈ U`, then
they coincide globally in `U`.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `eq_on_of_preconnected_of_eventually_eq`. -/
theorem eq_on_of_preconnected_of_frequently_eq (hf : analytic_on 𝕜 f U) (hg : analytic_on 𝕜 g U)
  (hU : is_preconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) :
  eq_on f g U :=
begin
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 := hfg.mono (λ z h, by rw [pi.sub_apply, h, sub_self]),
  simpa [sub_eq_zero] using
    λ z hz, (hf.sub hg).eq_on_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz
end

theorem eq_on_of_preconnected_of_mem_closure (hf : analytic_on 𝕜 f U) (hg : analytic_on 𝕜 g U)
  (hU : is_preconnected U) (h₀ : z₀ ∈ U) (hfg : z₀ ∈ closure ({z | f z = g z} \ {z₀})) :
  eq_on f g U :=
hf.eq_on_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

end analytic_on

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
* `analytic_at.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
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

lemma coef_order_ne_zero {n : ℕ} (ho : p.order = n) : p.coef n ≠ 0 :=
begin
  by_cases (∀ n, coef p n = 0),
  { simp [order, h] at ho; cases ho },
  { simp [order, h] at ho,
    norm_cast at ho,
    exact ((nat.find_eq_iff _).mp ho).1 }
end

lemma coef_eq_0_of_lt_order {n : ℕ} (ho : p.order = n) ⦃k : ℕ⦄ (hk : k < n) : p.coef k = 0 :=
begin
  by_cases (∀ n, coef p n = 0),
  { exact h k },
  { simp [order, h] at ho,
    norm_cast at ho,
    exact not_not.mp (((nat.find_eq_iff _).mp ho).2 k hk) }
end

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

@[simp] lemma coef_iterate_fslope (k n : ℕ) :
  (fslope^[k] p).coef n = p.coef (n + k) :=
by induction k with k ih generalizing p; refl <|> simpa [ih]

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

namespace has_sum

variables {a : ℕ → E}

lemma has_sum_at_zero (a : ℕ → E) : has_sum (λ n, (0:𝕜) ^ n • a n) (a 0) :=
by convert has_sum_single 0 (λ b h, _); simp [nat.pos_of_ne_zero h] <|> simp

/-- A variant of the `has_sum` predicate that states a property of the sum rather than its value.
`has_sum_in f {s}` is equivalent to `has_sum f s`. -/
def has_sum_in (a : ℕ → E) (S : set E) : Prop := ∃ s ∈ S, has_sum a s

lemma factor (hs : has_sum (λ m, z ^ m • a m) s) (ha : ∀ k < n, a k = 0) :
  has_sum_in (λ m, z ^ m • a (m + n)) {t | z ^ n • t = s} :=
begin
  refine dite (n = 0) (λ hn, by { subst n; simpa [has_sum_in] }) (λ hn, _),
  replace hn := nat.pos_of_ne_zero hn,
  by_cases (z = 0),
  { have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using has_sum_at_zero a),
    exact ⟨a n, by simp [h, hn, this], by simpa [h] using has_sum_at_zero (λ m, a (m + n))⟩ },
  { refine ⟨(z ^ n)⁻¹ • s, by field_simp [smul_smul], _⟩,
    have h1 : ∑ i in finset.range n, z ^ i • a i = 0,
      from finset.sum_eq_zero (λ k hk, by simp [ha k (finset.mem_range.mp hk)]),
    have h2 : has_sum (λ m, z ^ (m + n) • a (m + n)) s,
      by simpa [h1] using (has_sum_nat_add_iff' n).mpr hs,
    convert @has_sum.const_smul E ℕ 𝕜 _ _ _ _ _ _ _ (z⁻¹ ^ n) h2,
    field_simp [pow_add, smul_smul], simp only [inv_pow] }
end

end has_sum

namespace has_fpower_series_at

open formal_multilinear_series emetric

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`has_fpower_series_at` depends on `p.radius`. -/
lemma _root_.has_fpower_series_at_iff : has_fpower_series_at f p z₀ ↔
  ∀ᶠ z in 𝓝 0, has_sum (λ n, z ^ n • p.coef n) (f (z₀ + z)) :=
begin
  refine ⟨λ ⟨r, r_le, r_pos, h⟩, eventually_of_mem (ball_mem_nhds 0 r_pos)
    (λ _, by simpa using h), _⟩,
  simp only [metric.eventually_nhds_iff],
  rintro ⟨r, r_pos, h⟩,
  refine ⟨p.radius ⊓ r.to_nnreal, by simp, _, _⟩,
  { simp only [r_pos.lt, lt_inf_iff, ennreal.coe_pos, real.to_nnreal_pos, and_true],
    obtain ⟨z, z_pos, le_z⟩ := normed_field.exists_norm_lt 𝕜 r_pos.lt,
    have : (∥z∥₊ : ennreal) ≤ p.radius,
    by { simp only [dist_zero_right] at h,
      apply formal_multilinear_series.le_radius_of_tendsto,
      convert tendsto_norm.comp (h le_z).summable.tendsto_at_top_zero,
      funext; simp [norm_smul, mul_comm] },
    refine lt_of_lt_of_le _ this,
    simp only [ennreal.coe_pos],
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos)) },
  { simp only [mem_ball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coef, and_imp,
      dist_zero_right] at h ⊢,
    refine λ y hyp hyr, h _,
    simpa [nndist_eq_nnnorm, real.lt_to_nnreal_iff_coe_lt] using hyr }
end

lemma _root_.has_fpower_series_at_iff' : has_fpower_series_at f p z₀ ↔
  ∀ᶠ z in 𝓝 z₀, has_sum (λ n, (z - z₀) ^ n • p.coef n) (f z) :=
begin
  rw has_fpower_series_at_iff,
  split; intro h,
  { have : tendsto (λ z, z - z₀) (𝓝 z₀) (𝓝 0) := sub_self z₀ ▸ filter.tendsto_id.sub_const z₀,
    simpa using this.eventually h },
  { have : tendsto (λ z, z + z₀) (𝓝 0) (𝓝 (0 + z₀)) := filter.tendsto_id.add_const z₀,
    rw [zero_add] at this,
    simpa [add_comm] using this.eventually h }
end

lemma locally_zero_of_order_eq_top' (hp : has_fpower_series_at f p z₀) (h : p.order = ⊤) :
  ∀ᶠ z in 𝓝 0, f (z₀ + z) = 0 :=
begin
  have : ∀ᶠ z in 𝓝 0, has_sum (λ n, (0:E)) (f (z₀ + z)),
    by simpa [has_fpower_series_at_iff, order_eq_top_iff.mp h] using hp,
  exact this.mono (λ x hx, has_sum.unique hx has_sum_zero)
end

lemma locally_zero_of_order_eq_top (hp : has_fpower_series_at f p z₀) (h : p.order = ⊤) :
  ∀ᶠ z in 𝓝 z₀, f z = 0 :=
begin
  have : tendsto (λ z, z - z₀) (𝓝 z₀) (𝓝 0) := sub_self z₀ ▸ filter.tendsto_id.sub_const z₀,
  simpa using this.eventually (locally_zero_of_order_eq_top' hp h)
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

lemma has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : has_fpower_series_at f p z₀) :
  has_fpower_series_at ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ :=
begin
  induction n with n ih generalizing f p,
  { exact hp },
  { simpa using ih (has_fpower_series_dslope_fslope hp) }
end

lemma iterate_dslope_fslope_ne_zero (hp : has_fpower_series_at f p z₀) {n : ℕ} (h : p.order = n) :
  (swap dslope z₀)^[n] f z₀ ≠ 0 :=
begin
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope n hp) 1],
  simpa using coef_order_ne_zero h,
end

lemma eq_pow_order_mul_iterate_dslope (hp : has_fpower_series_at f p z₀) {n : ℕ} (h : p.order = n) :
  ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • ((swap dslope z₀)^[n] f z) :=
begin
  have hq := has_fpower_series_at_iff'.mp (has_fpower_series_iterate_dslope_fslope n hp),
  apply (hq.and (has_fpower_series_at_iff'.mp hp)).mono,
  rintro x ⟨hx1, hx2⟩,
  obtain ⟨s, hs1, hs2⟩ := has_sum.factor hx2 (coef_eq_0_of_lt_order h),
  convert hs1.symm,
  simp only [coef_iterate_fslope] at hx1,
  exact hx1.unique hs2
end

lemma locally_ne_zero_aux (hp : has_fpower_series_at f p z₀) {n : ℕ} (h : p.order = n) :
  ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
begin
  have h1 := set.mem_compl_singleton_iff.mpr (iterate_dslope_fslope_ne_zero hp h),
  have h2 := (has_fpower_series_iterate_dslope_fslope n hp).continuous_at.tendsto,
  have h3 := h2.eventually (is_open_compl_singleton.eventually_mem h1),
  refine eventually_nhds_within_iff.mpr ((h3.and (eq_pow_order_mul_iterate_dslope hp h)).mono _),
  rintro x ⟨ha, hb⟩ hc,
  simp only [← @sub_eq_zero _ _ x z₀, set.mem_compl_eq, set.mem_singleton_iff] at ha hc,
  simp [ha, hb, hc, pow_ne_zero],
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

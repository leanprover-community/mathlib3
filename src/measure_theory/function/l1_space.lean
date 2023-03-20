/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import measure_theory.function.lp_order


/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `mem_ℒp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `mem_ℒp 1`

In the second part, we establish an API between `integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `measure_space` and `β` is a
  `normed_add_comm_group` with a `second_countable_topology`. `f : α →ₘ β` is a "function" in `L¹`.
  In comments, `[f]` is also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_add_comm_group`.
  Then `has_finite_integral f` means `(∫⁻ a, ‖f a‖₊) < ∞`.

* If `β` is moreover a `measurable_space` then `f` is called `integrable` if
  `f` is `measurable` and `has_finite_integral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`integrable.induction` in the file `set_integral`.

## Tags

integrable, function space, l1

-/

noncomputable theory

open_locale classical topology big_operators ennreal measure_theory nnreal

open set filter topological_space ennreal emetric measure_theory

variables {α β γ δ : Type*} {m : measurable_space α} {μ ν : measure α} [measurable_space δ]
variables [normed_add_comm_group β]
variables [normed_add_comm_group γ]

namespace measure_theory

/-! ### Some results about the Lebesgue integral involving a normed group -/

lemma lintegral_nnnorm_eq_lintegral_edist (f : α → β) :
  ∫⁻ a, ‖f a‖₊ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ :=
by simp only [edist_eq_coe_nnnorm]

lemma lintegral_norm_eq_lintegral_edist (f : α → β) :
  ∫⁻ a, (ennreal.of_real ‖f a‖) ∂μ = ∫⁻ a, edist (f a) 0 ∂μ :=
by simp only [of_real_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm]

lemma lintegral_edist_triangle {f g h : α → β}
  (hf : ae_strongly_measurable f μ) (hh : ae_strongly_measurable h μ) :
  ∫⁻ a, edist (f a) (g a) ∂μ ≤ ∫⁻ a, edist (f a) (h a) ∂μ + ∫⁻ a, edist (g a) (h a) ∂μ :=
begin
  rw ← lintegral_add_left' (hf.edist hh),
  refine lintegral_mono (λ a, _),
  apply edist_triangle_right
end

lemma lintegral_nnnorm_zero : ∫⁻ a : α, ‖(0 : β)‖₊ ∂μ = 0 := by simp

lemma lintegral_nnnorm_add_left
  {f : α → β} (hf : ae_strongly_measurable f μ) (g : α → γ) :
  ∫⁻ a, ‖f a‖₊ + ‖g a‖₊ ∂μ = ∫⁻ a, ‖f a‖₊ ∂μ + ∫⁻ a, ‖g a‖₊ ∂μ :=
lintegral_add_left' hf.ennnorm _

lemma lintegral_nnnorm_add_right
  (f : α → β) {g : α → γ} (hg : ae_strongly_measurable g μ) :
  ∫⁻ a, ‖f a‖₊ + ‖g a‖₊ ∂μ = ∫⁻ a, ‖f a‖₊ ∂μ + ∫⁻ a, ‖g a‖₊ ∂μ :=
lintegral_add_right' _ hg.ennnorm

lemma lintegral_nnnorm_neg {f : α → β} :
  ∫⁻ a, ‖(-f) a‖₊ ∂μ = ∫⁻ a, ‖f a‖₊ ∂μ :=
by simp only [pi.neg_apply, nnnorm_neg]

/-! ### The predicate `has_finite_integral` -/

/-- `has_finite_integral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `has_finite_integral f` means `has_finite_integral f volume`. -/
def has_finite_integral {m : measurable_space α} (f : α → β) (μ : measure α . volume_tac) : Prop :=
∫⁻ a, ‖f a‖₊ ∂μ < ∞

lemma has_finite_integral_iff_norm (f : α → β) :
  has_finite_integral f μ ↔ ∫⁻ a, (ennreal.of_real ‖f a‖) ∂μ < ∞ :=
by simp only [has_finite_integral, of_real_norm_eq_coe_nnnorm]

lemma has_finite_integral_iff_edist (f : α → β) :
  has_finite_integral f μ ↔ ∫⁻ a, edist (f a) 0 ∂μ < ∞ :=
by simp only [has_finite_integral_iff_norm, edist_dist, dist_zero_right]

lemma has_finite_integral_iff_of_real {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
  has_finite_integral f μ ↔ ∫⁻ a, ennreal.of_real (f a) ∂μ < ∞ :=
by rw [has_finite_integral, lintegral_nnnorm_eq_of_ae_nonneg h]

lemma has_finite_integral_iff_of_nnreal {f : α → ℝ≥0} :
  has_finite_integral (λ x, (f x : ℝ)) μ ↔ ∫⁻ a, f a ∂μ < ∞ :=
by simp [has_finite_integral_iff_norm]

lemma has_finite_integral.mono {f : α → β} {g : α → γ} (hg : has_finite_integral g μ)
  (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : has_finite_integral f μ :=
begin
  simp only [has_finite_integral_iff_norm] at *,
  calc ∫⁻ a, (ennreal.of_real ‖f a‖) ∂μ ≤ ∫⁻ (a : α), (ennreal.of_real ‖g a‖) ∂μ :
    lintegral_mono_ae (h.mono $ assume a h, of_real_le_of_real h)
    ... < ∞ : hg
end

lemma has_finite_integral.mono' {f : α → β} {g : α → ℝ} (hg : has_finite_integral g μ)
  (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : has_finite_integral f μ :=
hg.mono $ h.mono $ λ x hx, le_trans hx (le_abs_self _)

lemma has_finite_integral.congr' {f : α → β} {g : α → γ} (hf : has_finite_integral f μ)
  (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
  has_finite_integral g μ :=
hf.mono $ eventually_eq.le $ eventually_eq.symm h

lemma has_finite_integral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
⟨λ hf, hf.congr' h, λ hg, hg.congr' $ eventually_eq.symm h⟩

lemma has_finite_integral.congr {f g : α → β} (hf : has_finite_integral f μ) (h : f =ᵐ[μ] g) :
  has_finite_integral g μ :=
hf.congr' $ h.fun_comp norm

lemma has_finite_integral_congr {f g : α → β} (h : f =ᵐ[μ] g) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
has_finite_integral_congr' $ h.fun_comp norm

lemma has_finite_integral_const_iff {c : β} :
  has_finite_integral (λ x : α, c) μ ↔ c = 0 ∨ μ univ < ∞ :=
by simp [has_finite_integral, lintegral_const, lt_top_iff_ne_top, ennreal.mul_eq_top,
  or_iff_not_imp_left]

lemma has_finite_integral_const [is_finite_measure μ] (c : β) :
  has_finite_integral (λ x : α, c) μ :=
has_finite_integral_const_iff.2 (or.inr $ measure_lt_top _ _)

lemma has_finite_integral_of_bounded [is_finite_measure μ] {f : α → β} {C : ℝ}
  (hC : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) : has_finite_integral f μ :=
(has_finite_integral_const C).mono' hC

lemma has_finite_integral.mono_measure {f : α → β} (h : has_finite_integral f ν) (hμ : μ ≤ ν) :
  has_finite_integral f μ :=
lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

lemma has_finite_integral.add_measure {f : α → β} (hμ : has_finite_integral f μ)
  (hν : has_finite_integral f ν) : has_finite_integral f (μ + ν) :=
begin
  simp only [has_finite_integral, lintegral_add_measure] at *,
  exact add_lt_top.2 ⟨hμ, hν⟩
end

lemma has_finite_integral.left_of_add_measure {f : α → β} (h : has_finite_integral f (μ + ν)) :
  has_finite_integral f μ :=
h.mono_measure $ measure.le_add_right $ le_rfl

lemma has_finite_integral.right_of_add_measure {f : α → β} (h : has_finite_integral f (μ + ν)) :
  has_finite_integral f ν :=
h.mono_measure $ measure.le_add_left $ le_rfl

@[simp] lemma has_finite_integral_add_measure {f : α → β} :
  has_finite_integral f (μ + ν) ↔ has_finite_integral f μ ∧ has_finite_integral f ν :=
⟨λ h, ⟨h.left_of_add_measure, h.right_of_add_measure⟩, λ h, h.1.add_measure h.2⟩

lemma has_finite_integral.smul_measure {f : α → β} (h : has_finite_integral f μ) {c : ℝ≥0∞}
  (hc : c ≠ ∞) : has_finite_integral f (c • μ) :=
begin
  simp only [has_finite_integral, lintegral_smul_measure] at *,
  exact mul_lt_top hc h.ne
end

@[simp] lemma has_finite_integral_zero_measure {m : measurable_space α} (f : α → β) :
  has_finite_integral f (0 : measure α) :=
by simp only [has_finite_integral, lintegral_zero_measure, with_top.zero_lt_top]

variables (α β μ)
@[simp] lemma has_finite_integral_zero : has_finite_integral (λa:α, (0:β)) μ :=
by simp [has_finite_integral]
variables {α β μ}

lemma has_finite_integral.neg {f : α → β} (hfi : has_finite_integral f μ) :
  has_finite_integral (-f) μ :=
by simpa [has_finite_integral] using hfi

@[simp] lemma has_finite_integral_neg_iff {f : α → β} :
  has_finite_integral (-f) μ ↔ has_finite_integral f μ :=
⟨λ h, neg_neg f ▸ h.neg, has_finite_integral.neg⟩

lemma has_finite_integral.norm {f : α → β} (hfi : has_finite_integral f μ) :
  has_finite_integral (λa, ‖f a‖) μ :=
have eq : (λa, (nnnorm ‖f a‖ : ℝ≥0∞)) = λa, (‖f a‖₊ : ℝ≥0∞),
  by { funext, rw nnnorm_norm },
by { rwa [has_finite_integral, eq] }

lemma has_finite_integral_norm_iff (f : α → β) :
  has_finite_integral (λa, ‖f a‖) μ ↔ has_finite_integral f μ :=
has_finite_integral_congr' $ eventually_of_forall $ λ x, norm_norm (f x)

lemma has_finite_integral_to_real_of_lintegral_ne_top
  {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
  has_finite_integral (λ x, (f x).to_real) μ :=
begin
  have : ∀ x, (‖(f x).to_real‖₊ : ℝ≥0∞) =
    @coe ℝ≥0 ℝ≥0∞ _ (⟨(f x).to_real, ennreal.to_real_nonneg⟩ : ℝ≥0),
  { intro x, rw real.nnnorm_of_nonneg },
  simp_rw [has_finite_integral, this],
  refine lt_of_le_of_lt (lintegral_mono (λ x, _)) (lt_top_iff_ne_top.2 hf),
  by_cases hfx : f x = ∞,
  { simp [hfx] },
  { lift f x to ℝ≥0 using hfx with fx,
    simp [← h] }
end

lemma is_finite_measure_with_density_of_real {f : α → ℝ} (hfi : has_finite_integral f μ) :
  is_finite_measure (μ.with_density (λ x, ennreal.of_real $ f x)) :=
begin
  refine is_finite_measure_with_density ((lintegral_mono $ λ x, _).trans_lt hfi).ne,
  exact real.of_real_le_ennnorm (f x)
end

section dominated_convergence

variables {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

lemma all_ae_of_real_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) :
  ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ‖F n a‖ ≤ ennreal.of_real (bound a) :=
λn, (h n).mono $ λ a h, ennreal.of_real_le_of_real h

lemma all_ae_tendsto_of_real_norm (h : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top $ 𝓝 $ f a) :
  ∀ᵐ a ∂μ, tendsto (λn, ennreal.of_real ‖F n a‖) at_top $ 𝓝 $ ennreal.of_real ‖f a‖ :=
h.mono $
  λ a h, tendsto_of_real $ tendsto.comp (continuous.tendsto continuous_norm _) h

lemma all_ae_of_real_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  ∀ᵐ a ∂μ, ennreal.of_real ‖f a‖ ≤ ennreal.of_real (bound a) :=
begin
  have F_le_bound := all_ae_of_real_F_le_bound h_bound,
  rw ← ae_all_iff at F_le_bound,
  apply F_le_bound.mp ((all_ae_tendsto_of_real_norm h_lim).mono _),
  assume a tendsto_norm F_le_bound,
  exact le_of_tendsto' tendsto_norm (F_le_bound)
end

lemma has_finite_integral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (bound_has_finite_integral : has_finite_integral bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  has_finite_integral f μ :=
/- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
  and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
begin
  rw has_finite_integral_iff_norm,
  calc ∫⁻ a, (ennreal.of_real ‖f a‖) ∂μ ≤ ∫⁻ a, ennreal.of_real (bound a) ∂μ :
    lintegral_mono_ae $ all_ae_of_real_f_le_bound h_bound h_lim
    ... < ∞ :
    begin
      rw ← has_finite_integral_iff_of_real,
      { exact bound_has_finite_integral },
      exact (h_bound 0).mono (λ a h, le_trans (norm_nonneg _) h)
    end
end

lemma tendsto_lintegral_norm_of_dominated_convergence
  {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (F_measurable : ∀ n, ae_strongly_measurable (F n) μ)
  (bound_has_finite_integral : has_finite_integral bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, (ennreal.of_real ‖F n a - f a‖) ∂μ) at_top (𝓝 0) :=
have f_measurable : ae_strongly_measurable f μ :=
  ae_strongly_measurable_of_tendsto_ae _ F_measurable h_lim,
let b := λ a, 2 * ennreal.of_real (bound a) in
/- `‖F n a‖ ≤ bound a` and `F n a --> f a` implies `‖f a‖ ≤ bound a`, and thus by the
  triangle inequality, have `‖F n a - f a‖ ≤ 2 * (bound a). -/
have hb : ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ‖F n a - f a‖ ≤ b a,
begin
  assume n,
  filter_upwards [all_ae_of_real_F_le_bound h_bound n, all_ae_of_real_f_le_bound h_bound h_lim]
    with a h₁ h₂,
  calc ennreal.of_real ‖F n a - f a‖ ≤ (ennreal.of_real ‖F n a‖) + (ennreal.of_real ‖f a‖) :
  begin
    rw [← ennreal.of_real_add],
    apply of_real_le_of_real,
    { apply norm_sub_le }, { exact norm_nonneg _ }, { exact norm_nonneg _ }
  end
    ... ≤ (ennreal.of_real (bound a)) + (ennreal.of_real (bound a)) : add_le_add h₁ h₂
    ... = b a : by rw ← two_mul
end,
/- On the other hand, `F n a --> f a` implies that `‖F n a - f a‖ --> 0`  -/
have h : ∀ᵐ a ∂μ, tendsto (λ n, ennreal.of_real ‖F n a - f a‖) at_top (𝓝 0),
begin
  rw ← ennreal.of_real_zero,
  refine h_lim.mono (λ a h, (continuous_of_real.tendsto _).comp _),
  rwa ← tendsto_iff_norm_tendsto_zero
end,
/- Therefore, by the dominated convergence theorem for nonnegative integration, have
  ` ∫ ‖f a - F n a‖ --> 0 ` -/
begin
  suffices h : tendsto (λn, ∫⁻ a, (ennreal.of_real ‖F n a - f a‖) ∂μ) at_top (𝓝 (∫⁻ (a:α), 0 ∂μ)),
  { rwa lintegral_zero at h },
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence' _ _ hb _ _,
  -- Show `λa, ‖f a - F n a‖` is almost everywhere measurable for all `n`
  { exact λ n,  measurable_of_real.comp_ae_measurable
      ((F_measurable n).sub f_measurable).norm.ae_measurable },
  -- Show `2 * bound` is has_finite_integral
  { rw has_finite_integral_iff_of_real at bound_has_finite_integral,
    { calc ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ennreal.of_real (bound a) ∂μ :
        by { rw lintegral_const_mul', exact coe_ne_top }
        ... ≠ ∞ : mul_ne_top coe_ne_top bound_has_finite_integral.ne },
    filter_upwards [h_bound 0] with _ h using le_trans (norm_nonneg _) h },
  -- Show `‖f a - F n a‖ --> 0`
  { exact h }
end

end dominated_convergence

section pos_part
/-! Lemmas used for defining the positive part of a `L¹` function -/

lemma has_finite_integral.max_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (λa, max (f a) 0) μ :=
hf.mono $ eventually_of_forall $ λ x, by simp [abs_le, le_abs_self]

lemma has_finite_integral.min_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (λa, min (f a) 0) μ :=
hf.mono $ eventually_of_forall $ λ x,
  by simp [abs_le, neg_le, neg_le_abs_self, abs_eq_max_neg, le_total]

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma has_finite_integral.smul (c : 𝕜) {f : α → β} : has_finite_integral f μ →
  has_finite_integral (c • f) μ :=
begin
  simp only [has_finite_integral], assume hfi,
  calc
    ∫⁻ (a : α), ‖c • f a‖₊ ∂μ = ∫⁻ (a : α), (‖c‖₊) * ‖f a‖₊ ∂μ :
      by simp only [nnnorm_smul, ennreal.coe_mul]
    ... < ∞ :
    begin
      rw lintegral_const_mul',
      exacts [mul_lt_top coe_ne_top hfi.ne, coe_ne_top]
    end
end

lemma has_finite_integral_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  has_finite_integral (c • f) μ ↔ has_finite_integral f μ :=
begin
  split,
  { assume h,
    simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.smul c⁻¹ },
  exact has_finite_integral.smul _
end

lemma has_finite_integral.const_mul {f : α → ℝ} (h : has_finite_integral f μ) (c : ℝ) :
  has_finite_integral (λ x, c * f x) μ :=
(has_finite_integral.smul c h : _)

lemma has_finite_integral.mul_const {f : α → ℝ} (h : has_finite_integral f μ) (c : ℝ) :
  has_finite_integral (λ x, f x * c) μ :=
by simp_rw [mul_comm, h.const_mul _]

end normed_space

/-! ### The predicate `integrable` -/

-- variables [measurable_space β] [measurable_space γ] [measurable_space δ]

/-- `integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `integrable f` means `integrable f volume`. -/
def integrable {α} {m : measurable_space α} (f : α → β) (μ : measure α . volume_tac) : Prop :=
ae_strongly_measurable f μ ∧ has_finite_integral f μ

lemma mem_ℒp_one_iff_integrable {f : α → β} : mem_ℒp f 1 μ ↔ integrable f μ :=
by simp_rw [integrable, has_finite_integral, mem_ℒp, snorm_one_eq_lintegral_nnnorm]

lemma integrable.ae_strongly_measurable {f : α → β} (hf : integrable f μ) :
  ae_strongly_measurable f μ :=
hf.1

lemma integrable.ae_measurable [measurable_space β] [borel_space β]
  {f : α → β} (hf : integrable f μ) :
  ae_measurable f μ :=
hf.ae_strongly_measurable.ae_measurable

lemma integrable.has_finite_integral {f : α → β} (hf : integrable f μ) : has_finite_integral f μ :=
hf.2

lemma integrable.mono {f : α → β} {g : α → γ}
  (hg : integrable g μ) (hf : ae_strongly_measurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) :
  integrable f μ :=
⟨hf, hg.has_finite_integral.mono h⟩

lemma integrable.mono' {f : α → β} {g : α → ℝ}
  (hg : integrable g μ) (hf : ae_strongly_measurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) :
  integrable f μ :=
⟨hf, hg.has_finite_integral.mono' h⟩

lemma integrable.congr' {f : α → β} {g : α → γ}
  (hf : integrable f μ) (hg : ae_strongly_measurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
  integrable g μ :=
⟨hg, hf.has_finite_integral.congr' h⟩

lemma integrable_congr' {f : α → β} {g : α → γ}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
  integrable f μ ↔ integrable g μ :=
⟨λ h2f, h2f.congr' hg h, λ h2g, h2g.congr' hf $ eventually_eq.symm h⟩

lemma integrable.congr {f g : α → β} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  integrable g μ :=
⟨hf.1.congr h, hf.2.congr h⟩

lemma integrable_congr {f g : α → β} (h : f =ᵐ[μ] g) :
  integrable f μ ↔ integrable g μ :=
⟨λ hf, hf.congr h, λ hg, hg.congr h.symm⟩

lemma integrable_const_iff {c : β} : integrable (λ x : α, c) μ ↔ c = 0 ∨ μ univ < ∞ :=
begin
  have : ae_strongly_measurable (λ (x : α), c) μ := ae_strongly_measurable_const,
  rw [integrable, and_iff_right this, has_finite_integral_const_iff]
end

lemma integrable_const [is_finite_measure μ] (c : β) : integrable (λ x : α, c) μ :=
integrable_const_iff.2 $ or.inr $ measure_lt_top _ _

lemma mem_ℒp.integrable_norm_rpow {f : α → β} {p : ℝ≥0∞}
  (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  integrable (λ (x : α), ‖f x‖ ^ p.to_real) μ :=
begin
  rw ← mem_ℒp_one_iff_integrable,
  exact hf.norm_rpow hp_ne_zero hp_ne_top,
end

lemma mem_ℒp.integrable_norm_rpow' [is_finite_measure μ] {f : α → β} {p : ℝ≥0∞}
  (hf : mem_ℒp f p μ) :
  integrable (λ (x : α), ‖f x‖ ^ p.to_real) μ :=
begin
  by_cases h_zero : p = 0,
  { simp [h_zero, integrable_const] },
  by_cases h_top : p = ∞,
  { simp [h_top, integrable_const] },
  exact hf.integrable_norm_rpow h_zero h_top
end

lemma integrable.mono_measure {f : α → β} (h : integrable f ν) (hμ : μ ≤ ν) : integrable f μ :=
⟨h.ae_strongly_measurable.mono_measure hμ, h.has_finite_integral.mono_measure hμ⟩

lemma integrable.of_measure_le_smul {μ' : measure α} (c : ℝ≥0∞) (hc : c ≠ ∞)
  (hμ'_le : μ' ≤ c • μ) {f : α → β} (hf : integrable f μ) :
  integrable f μ' :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.of_measure_le_smul c hc hμ'_le, }

lemma integrable.add_measure {f : α → β} (hμ : integrable f μ) (hν : integrable f ν) :
  integrable f (μ + ν) :=
begin
  simp_rw ← mem_ℒp_one_iff_integrable at hμ hν ⊢,
  refine ⟨hμ.ae_strongly_measurable.add_measure hν.ae_strongly_measurable, _⟩,
  rw [snorm_one_add_measure, ennreal.add_lt_top],
  exact ⟨hμ.snorm_lt_top, hν.snorm_lt_top⟩,
end

lemma integrable.left_of_add_measure {f : α → β} (h : integrable f (μ + ν)) : integrable f μ :=
by { rw ← mem_ℒp_one_iff_integrable at h ⊢, exact h.left_of_add_measure, }

lemma integrable.right_of_add_measure {f : α → β} (h : integrable f (μ + ν)) : integrable f ν :=
by { rw ← mem_ℒp_one_iff_integrable at h ⊢, exact h.right_of_add_measure, }

@[simp] lemma integrable_add_measure {f : α → β} :
  integrable f (μ + ν) ↔ integrable f μ ∧ integrable f ν :=
⟨λ h, ⟨h.left_of_add_measure, h.right_of_add_measure⟩, λ h, h.1.add_measure h.2⟩

@[simp] lemma integrable_zero_measure {m : measurable_space α} {f : α → β} :
  integrable f (0 : measure α) :=
⟨ae_strongly_measurable_zero_measure f, has_finite_integral_zero_measure f⟩

theorem integrable_finset_sum_measure {ι} {m : measurable_space α} {f : α → β}
  {μ : ι → measure α} {s : finset ι} :
  integrable f (∑ i in s, μ i) ↔ ∀ i ∈ s, integrable f (μ i) :=
by induction s using finset.induction_on; simp [*]

lemma integrable.smul_measure {f : α → β} (h : integrable f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
  integrable f (c • μ) :=
by { rw ← mem_ℒp_one_iff_integrable at h ⊢, exact h.smul_measure hc, }

lemma integrable_smul_measure {f : α → β} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
  integrable f (c • μ) ↔ integrable f μ :=
⟨λ h, by simpa only [smul_smul, ennreal.inv_mul_cancel h₁ h₂, one_smul]
  using h.smul_measure (ennreal.inv_ne_top.2 h₁), λ h, h.smul_measure h₂⟩

lemma integrable_inv_smul_measure {f : α → β} {c : ℝ≥0∞} (h₁ : c ≠ 0) (h₂ : c ≠ ∞) :
  integrable f (c⁻¹ • μ) ↔ integrable f μ :=
integrable_smul_measure (by simpa using h₂) (by simpa using h₁)

lemma integrable.to_average {f : α → β} (h : integrable f μ) :
  integrable f ((μ univ)⁻¹ • μ) :=
begin
  rcases eq_or_ne μ 0 with rfl|hne,
  { rwa smul_zero },
  { apply h.smul_measure, simpa }
end

lemma integrable_average [is_finite_measure μ] {f : α → β} :
  integrable f ((μ univ)⁻¹ • μ) ↔ integrable f μ :=
(eq_or_ne μ 0).by_cases (λ h, by simp [h]) $ λ h,
  integrable_smul_measure (ennreal.inv_ne_zero.2 $ measure_ne_top _ _)
    (ennreal.inv_ne_top.2 $ mt measure.measure_univ_eq_zero.1 h)

lemma integrable_map_measure {f : α → δ} {g : δ → β}
  (hg : ae_strongly_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable, exact mem_ℒp_map_measure_iff hg hf, }

lemma integrable.comp_ae_measurable {f : α → δ} {g : δ → β}
  (hg : integrable g (measure.map f μ)) (hf : ae_measurable f μ) : integrable (g ∘ f) μ :=
(integrable_map_measure hg.ae_strongly_measurable hf).mp hg

lemma integrable.comp_measurable {f : α → δ} {g : δ → β}
  (hg : integrable g (measure.map f μ)) (hf : measurable f) : integrable (g ∘ f) μ :=
hg.comp_ae_measurable hf.ae_measurable

lemma _root_.measurable_embedding.integrable_map_iff
  {f : α → δ} (hf : measurable_embedding f) {g : δ → β} :
  integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable, exact hf.mem_ℒp_map_measure_iff, }

lemma integrable_map_equiv (f : α ≃ᵐ δ) (g : δ → β) :
  integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable, exact f.mem_ℒp_map_measure_iff, }

lemma measure_preserving.integrable_comp {ν : measure δ} {g : δ → β}
  {f : α → δ} (hf : measure_preserving f μ ν) (hg : ae_strongly_measurable g ν) :
  integrable (g ∘ f) μ ↔ integrable g ν :=
by { rw ← hf.map_eq at hg ⊢, exact (integrable_map_measure hg hf.measurable.ae_measurable).symm }

lemma measure_preserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : measure_preserving f μ ν)
  (h₂ : measurable_embedding f) {g : δ → β} :
  integrable (g ∘ f) μ ↔ integrable g ν :=
h₁.map_eq ▸ iff.symm h₂.integrable_map_iff

lemma lintegral_edist_lt_top {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) :
  ∫⁻ a, edist (f a) (g a) ∂μ < ∞ :=
lt_of_le_of_lt
  (lintegral_edist_triangle hf.ae_strongly_measurable ae_strongly_measurable_zero)
  (ennreal.add_lt_top.2 $ by { simp_rw [pi.zero_apply, ← has_finite_integral_iff_edist],
                               exact ⟨hf.has_finite_integral, hg.has_finite_integral⟩ })

variables (α β μ)
@[simp] lemma integrable_zero : integrable (λ _, (0 : β)) μ :=
by simp [integrable, ae_strongly_measurable_const]
variables {α β μ}

lemma integrable.add' {f g : α → β} (hf : integrable f μ) (hg : integrable g μ) :
  has_finite_integral (f + g) μ :=
calc ∫⁻ a, ‖f a + g a‖₊ ∂μ ≤ ∫⁻ a, ‖f a‖₊ + ‖g a‖₊ ∂μ :
  lintegral_mono (λ a, by exact_mod_cast nnnorm_add_le _ _)
... = _ : lintegral_nnnorm_add_left hf.ae_strongly_measurable _
... < ∞ : add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩

lemma integrable.add
  {f g : α → β} (hf : integrable f μ) (hg : integrable g μ) : integrable (f + g) μ :=
⟨hf.ae_strongly_measurable.add hg.ae_strongly_measurable, hf.add' hg⟩

lemma integrable_finset_sum' {ι} (s : finset ι)
  {f : ι → α → β} (hf : ∀ i ∈ s, integrable (f i) μ) : integrable (∑ i in s, f i) μ :=
finset.sum_induction f (λ g, integrable g μ) (λ _ _, integrable.add)
  (integrable_zero _ _ _) hf

lemma integrable_finset_sum {ι} (s : finset ι)
  {f : ι → α → β} (hf : ∀ i ∈ s, integrable (f i) μ) : integrable (λ a, ∑ i in s, f i a) μ :=
by simpa only [← finset.sum_apply] using integrable_finset_sum' s hf

lemma integrable.neg {f : α → β} (hf : integrable f μ) : integrable (-f) μ :=
⟨hf.ae_strongly_measurable.neg, hf.has_finite_integral.neg⟩

@[simp] lemma integrable_neg_iff {f : α → β} :
  integrable (-f) μ ↔ integrable f μ :=
⟨λ h, neg_neg f ▸ h.neg, integrable.neg⟩

lemma integrable.sub {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) : integrable (f - g) μ :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma integrable.norm {f : α → β} (hf : integrable f μ) :
  integrable (λ a, ‖f a‖) μ :=
⟨hf.ae_strongly_measurable.norm, hf.has_finite_integral.norm⟩

lemma integrable.inf {β} [normed_lattice_add_comm_group β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⊓ g) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf hg ⊢, exact hf.inf hg, }

lemma integrable.sup {β} [normed_lattice_add_comm_group β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⊔ g) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf hg ⊢, exact hf.sup hg, }

lemma integrable.abs {β} [normed_lattice_add_comm_group β] {f : α → β} (hf : integrable f μ) :
  integrable (λ a, |f a|) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.abs, }

lemma integrable.bdd_mul {F : Type*} [normed_division_ring F]
  {f g : α → F} (hint : integrable g μ) (hm : ae_strongly_measurable f μ)
  (hfbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
  integrable (λ x, f x * g x) μ :=
begin
  casesI is_empty_or_nonempty α with hα hα,
  { rw μ.eq_zero_of_is_empty,
    exact integrable_zero_measure },
  { refine ⟨hm.mul hint.1, _⟩,
    obtain ⟨C, hC⟩ := hfbdd,
    have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC hα.some),
    have : (λ x, ‖f x * g x‖₊) ≤ λ x, ⟨C, hCnonneg⟩ * ‖g x‖₊,
    { intro x,
      simp only [nnnorm_mul],
      exact mul_le_mul_of_nonneg_right (hC x) (zero_le _) },
    refine lt_of_le_of_lt (lintegral_mono_nnreal this) _,
    simp only [ennreal.coe_mul],
    rw lintegral_const_mul' _ _ ennreal.coe_ne_top,
    exact ennreal.mul_lt_top ennreal.coe_ne_top (ne_of_lt hint.2) },
end

/-- Hölder's inequality for integrable functions: the scalar multiplication of an integrable
vector-valued function by a scalar function with finite essential supremum is integrable. -/
lemma integrable.ess_sup_smul {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β] {f : α → β}
  (hf : integrable f μ) {g : α → 𝕜} (g_ae_strongly_measurable : ae_strongly_measurable g μ)
  (ess_sup_g : ess_sup (λ x, (‖g x‖₊ : ℝ≥0∞)) μ ≠ ∞) :
  integrable (λ (x : α), g x • f x) μ :=
begin
  rw ← mem_ℒp_one_iff_integrable at *,
  refine ⟨g_ae_strongly_measurable.smul hf.1, _⟩,
  have h : (1:ℝ≥0∞) / 1 = 1 / ∞ + 1 / 1 := by norm_num,
  have hg' : snorm g ∞ μ ≠ ∞ := by rwa snorm_exponent_top,
  calc snorm (λ (x : α), g x • f x) 1 μ
      ≤ _ : measure_theory.snorm_smul_le_mul_snorm hf.1 g_ae_strongly_measurable h
  ... < ∞ : ennreal.mul_lt_top hg' hf.2.ne,
end

/-- Hölder's inequality for integrable functions: the scalar multiplication of an integrable
scalar-valued function by a vector-value function with finite essential supremum is integrable. -/
lemma integrable.smul_ess_sup {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β] {f : α → 𝕜}
  (hf : integrable f μ) {g : α → β} (g_ae_strongly_measurable : ae_strongly_measurable g μ)
  (ess_sup_g : ess_sup (λ x, (‖g x‖₊ : ℝ≥0∞)) μ ≠ ∞) :
  integrable (λ (x : α), f x • g x) μ :=
begin
  rw ← mem_ℒp_one_iff_integrable at *,
  refine ⟨hf.1.smul g_ae_strongly_measurable, _⟩,
  have h : (1:ℝ≥0∞) / 1 = 1 / 1 + 1 / ∞ := by norm_num,
  have hg' : snorm g ∞ μ ≠ ∞ := by rwa snorm_exponent_top,
  calc snorm (λ (x : α), f x • g x) 1 μ
      ≤ _ : measure_theory.snorm_smul_le_mul_snorm g_ae_strongly_measurable hf.1 h
  ... < ∞ : ennreal.mul_lt_top hf.2.ne hg',
end

lemma integrable_norm_iff {f : α → β} (hf : ae_strongly_measurable f μ) :
  integrable (λa, ‖f a‖) μ ↔ integrable f μ :=
by simp_rw [integrable, and_iff_right hf, and_iff_right hf.norm, has_finite_integral_norm_iff]

lemma integrable_of_norm_sub_le {f₀ f₁ : α → β} {g : α → ℝ}
  (hf₁_m : ae_strongly_measurable f₁ μ)
  (hf₀_i : integrable f₀ μ)
  (hg_i : integrable g μ)
  (h : ∀ᵐ a ∂μ, ‖f₀ a - f₁ a‖ ≤ g a) :
  integrable f₁ μ :=
begin
  have : ∀ᵐ a ∂μ, ‖f₁ a‖ ≤ ‖f₀ a‖ + g a,
  { apply h.mono,
    intros a ha,
    calc ‖f₁ a‖ ≤ ‖f₀ a‖ + ‖f₀ a - f₁ a‖ : norm_le_insert _ _
    ... ≤ ‖f₀ a‖ + g a : add_le_add_left ha _ },
  exact integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this
end

lemma integrable.prod_mk {f : α → β} {g : α → γ} (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ x, (f x, g x)) μ :=
⟨hf.ae_strongly_measurable.prod_mk hg.ae_strongly_measurable,
  (hf.norm.add' hg.norm).mono $ eventually_of_forall $ λ x,
  calc max ‖f x‖ ‖g x‖ ≤ ‖f x‖ + ‖g x‖   : max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
                 ... ≤ ‖(‖f x‖ + ‖g x‖)‖ : le_abs_self _⟩

lemma mem_ℒp.integrable {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → β} [is_finite_measure μ]
  (hfq : mem_ℒp f q μ) : integrable f μ :=
mem_ℒp_one_iff_integrable.mp (hfq.mem_ℒp_of_exponent_le hq1)

/-- A non-quantitative version of Markov inequality for integrable functions: the measure of points
where `‖f x‖ ≥ ε` is finite for all positive `ε`. -/
lemma integrable.measure_ge_lt_top {f : α → β} (hf : integrable f μ) {ε : ℝ} (hε : 0 < ε) :
  μ {x | ε ≤ ‖f x‖} < ∞ :=
begin
  rw show {x | ε ≤ ‖f x‖} = {x | ennreal.of_real ε ≤ ‖f x‖₊},
    by simp only [ennreal.of_real, real.to_nnreal_le_iff_le_coe, ennreal.coe_le_coe, coe_nnnorm],
  refine (meas_ge_le_mul_pow_snorm μ one_ne_zero ennreal.one_ne_top hf.1 _).trans_lt _,
  { simpa only [ne.def, ennreal.of_real_eq_zero, not_le] using hε },
  apply ennreal.mul_lt_top,
  { simpa only [ennreal.one_to_real, ennreal.rpow_one, ne.def, ennreal.inv_eq_top,
      ennreal.of_real_eq_zero, not_le] using hε },
  simpa only [ennreal.one_to_real, ennreal.rpow_one]
    using (mem_ℒp_one_iff_integrable.2 hf).snorm_ne_top,
end

lemma lipschitz_with.integrable_comp_iff_of_antilipschitz {K K'} {f : α → β} {g : β → γ}
  (hg : lipschitz_with K g) (hg' : antilipschitz_with K' g) (g0 : g 0 = 0) :
  integrable (g ∘ f) μ ↔ integrable f μ :=
by simp [← mem_ℒp_one_iff_integrable, hg.mem_ℒp_comp_iff_of_antilipschitz hg' g0]

lemma integrable.real_to_nnreal {f : α → ℝ} (hf : integrable f μ) :
  integrable (λ x, ((f x).to_nnreal : ℝ)) μ :=
begin
  refine ⟨hf.ae_strongly_measurable.ae_measurable
    .real_to_nnreal.coe_nnreal_real.ae_strongly_measurable, _⟩,
  rw has_finite_integral_iff_norm,
  refine lt_of_le_of_lt _ ((has_finite_integral_iff_norm _).1 hf.has_finite_integral),
  apply lintegral_mono,
  assume x,
  simp [ennreal.of_real_le_of_real, abs_le, le_abs_self],
end

lemma of_real_to_real_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
  (λ x, ennreal.of_real (f x).to_real) =ᵐ[μ] f :=
begin
  filter_upwards [hf],
  assume x hx,
  simp only [hx.ne, of_real_to_real, ne.def, not_false_iff],
end

lemma coe_to_nnreal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) :
  (λ x, ((f x).to_nnreal : ℝ≥0∞)) =ᵐ[μ] f :=
begin
  filter_upwards [hf],
  assume x hx,
  simp only [hx.ne, ne.def, not_false_iff, coe_to_nnreal],
end

section
variables  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

lemma integrable_with_density_iff_integrable_coe_smul
  {f : α → ℝ≥0} (hf : measurable f) {g : α → E} :
  integrable g (μ.with_density (λ x, f x)) ↔ integrable (λ x, (f x : ℝ) • g x) μ :=
begin
  by_cases H : ae_strongly_measurable (λ (x : α), (f x : ℝ) • g x) μ,
  { simp only [integrable, ae_strongly_measurable_with_density_iff hf, has_finite_integral, H,
      true_and],
    rw lintegral_with_density_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.ae_measurable,
    { congr',
      ext1 x,
      simp only [nnnorm_smul, nnreal.nnnorm_eq, coe_mul, pi.mul_apply] },
    { rw ae_measurable_with_density_ennreal_iff hf,
      convert H.ennnorm,
      ext1 x,
      simp only [nnnorm_smul, nnreal.nnnorm_eq, coe_mul] } },
  { simp only [integrable, ae_strongly_measurable_with_density_iff hf, H, false_and] }
end

lemma integrable_with_density_iff_integrable_smul {f : α → ℝ≥0} (hf : measurable f) {g : α → E} :
  integrable g (μ.with_density (λ x, f x)) ↔ integrable (λ x, f x • g x) μ :=
integrable_with_density_iff_integrable_coe_smul hf

lemma integrable_with_density_iff_integrable_smul'
  {f : α → ℝ≥0∞} (hf : measurable f) (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → E} :
  integrable g (μ.with_density f) ↔ integrable (λ x, (f x).to_real • g x) μ :=
begin
  rw [← with_density_congr_ae (coe_to_nnreal_ae_eq hflt),
      integrable_with_density_iff_integrable_smul],
  { refl },
  { exact hf.ennreal_to_nnreal },
end

lemma integrable_with_density_iff_integrable_coe_smul₀
  {f : α → ℝ≥0} (hf : ae_measurable f μ) {g : α → E} :
  integrable g (μ.with_density (λ x, f x)) ↔ integrable (λ x, (f x : ℝ) • g x) μ :=
calc
integrable g (μ.with_density (λ x, f x))
    ↔ integrable g (μ.with_density (λ x, hf.mk f x)) :
begin
  suffices : (λ x, (f x : ℝ≥0∞)) =ᵐ[μ] (λ x, hf.mk f x), by rw with_density_congr_ae this,
  filter_upwards [hf.ae_eq_mk] with x hx,
  simp [hx],
end
... ↔ integrable (λ x, (hf.mk f x : ℝ) • g x) μ :
  integrable_with_density_iff_integrable_coe_smul hf.measurable_mk
... ↔ integrable (λ x, (f x : ℝ) • g x) μ :
begin
  apply integrable_congr,
  filter_upwards [hf.ae_eq_mk] with x hx,
  simp [hx],
end

lemma integrable_with_density_iff_integrable_smul₀
  {f : α → ℝ≥0} (hf : ae_measurable f μ) {g : α → E} :
  integrable g (μ.with_density (λ x, f x)) ↔ integrable (λ x, f x • g x) μ :=
integrable_with_density_iff_integrable_coe_smul₀ hf

end

lemma integrable_with_density_iff {f : α → ℝ≥0∞} (hf : measurable f)
  (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → ℝ} :
  integrable g (μ.with_density f) ↔ integrable (λ x, g x * (f x).to_real) μ :=
begin
  have : (λ x, g x * (f x).to_real) = (λ x, (f x).to_real • g x), by simp [mul_comm],
  rw this,
  exact integrable_with_density_iff_integrable_smul' hf hflt,
end

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

lemma mem_ℒ1_smul_of_L1_with_density {f : α → ℝ≥0} (f_meas : measurable f)
  (u : Lp E 1 (μ.with_density (λ x, f x))) :
  mem_ℒp (λ x, f x • u x) 1 μ :=
mem_ℒp_one_iff_integrable.2 $ (integrable_with_density_iff_integrable_smul f_meas).1 $
mem_ℒp_one_iff_integrable.1 (Lp.mem_ℒp u)

variable (μ)
/-- The map `u ↦ f • u` is an isometry between the `L^1` spaces for `μ.with_density f` and `μ`. -/
noncomputable def with_density_smul_li {f : α → ℝ≥0} (f_meas : measurable f) :
  Lp E 1 (μ.with_density (λ x, f x)) →ₗᵢ[ℝ] Lp E 1 μ :=
{ to_fun := λ u, (mem_ℒ1_smul_of_L1_with_density f_meas u).to_Lp _,
  map_add' :=
  begin
    assume u v,
    ext1,
    filter_upwards [(mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp,
      (mem_ℒ1_smul_of_L1_with_density f_meas v).coe_fn_to_Lp,
      (mem_ℒ1_smul_of_L1_with_density f_meas (u + v)).coe_fn_to_Lp,
      Lp.coe_fn_add ((mem_ℒ1_smul_of_L1_with_density f_meas u).to_Lp _)
        ((mem_ℒ1_smul_of_L1_with_density f_meas v).to_Lp _),
      (ae_with_density_iff f_meas.coe_nnreal_ennreal).1 (Lp.coe_fn_add u v)],
    assume x hu hv huv h' h'',
    rw [huv, h', pi.add_apply, hu, hv],
    rcases eq_or_ne (f x) 0 with hx|hx,
    { simp only [hx, zero_smul, add_zero] },
    { rw [h'' _, pi.add_apply, smul_add],
      simpa only [ne.def, ennreal.coe_eq_zero] using hx }
  end,
  map_smul' :=
  begin
    assume r u,
    ext1,
    filter_upwards [(ae_with_density_iff f_meas.coe_nnreal_ennreal).1 (Lp.coe_fn_smul r u),
      (mem_ℒ1_smul_of_L1_with_density f_meas (r • u)).coe_fn_to_Lp,
      Lp.coe_fn_smul r ((mem_ℒ1_smul_of_L1_with_density f_meas u).to_Lp _),
      (mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp],
    assume x h h' h'' h''',
    rw [ring_hom.id_apply, h', h'', pi.smul_apply, h'''],
    rcases eq_or_ne (f x) 0 with hx|hx,
    { simp only [hx, zero_smul, smul_zero] },
    { rw [h _, smul_comm, pi.smul_apply],
      simpa only [ne.def, ennreal.coe_eq_zero] using hx }
  end,
  norm_map' :=
  begin
    assume u,
    simp only [snorm, linear_map.coe_mk, Lp.norm_to_Lp, one_ne_zero, ennreal.one_ne_top,
      ennreal.one_to_real, if_false, snorm', ennreal.rpow_one, _root_.div_one, Lp.norm_def],
    rw lintegral_with_density_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
      (filter.eventually_of_forall (λ x, ennreal.coe_lt_top)),
    congr' 1,
    apply lintegral_congr_ae,
    filter_upwards [(mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp] with x hx,
    rw [hx, pi.mul_apply],
    change ↑‖(f x : ℝ) • u x‖₊ = ↑(f x) * ↑‖u x‖₊,
    simp only [nnnorm_smul, nnreal.nnnorm_eq, ennreal.coe_mul],
  end }

@[simp] lemma with_density_smul_li_apply {f : α → ℝ≥0} (f_meas : measurable f)
  (u : Lp E 1 (μ.with_density (λ x, f x))) :
  with_density_smul_li μ f_meas u =
    (mem_ℒ1_smul_of_L1_with_density f_meas u).to_Lp (λ x, f x • u x) :=
rfl

end

lemma mem_ℒ1_to_real_of_lintegral_ne_top
  {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
  mem_ℒp (λ x, (f x).to_real) 1 μ :=
begin
  rw [mem_ℒp, snorm_one_eq_lintegral_nnnorm],
  exact ⟨(ae_measurable.ennreal_to_real hfm).ae_strongly_measurable,
          has_finite_integral_to_real_of_lintegral_ne_top hfi⟩
end

lemma integrable_to_real_of_lintegral_ne_top
  {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
  integrable (λ x, (f x).to_real) μ :=
mem_ℒp_one_iff_integrable.1 $ mem_ℒ1_to_real_of_lintegral_ne_top hfm hfi

section pos_part
/-! ### Lemmas used for defining the positive part of a `L¹` function -/

lemma integrable.pos_part {f : α → ℝ} (hf : integrable f μ) : integrable (λ a, max (f a) 0) μ :=
⟨(hf.ae_strongly_measurable.ae_measurable.max ae_measurable_const).ae_strongly_measurable,
  hf.has_finite_integral.max_zero⟩

lemma integrable.neg_part {f : α → ℝ} (hf : integrable f μ) : integrable (λ a, max (-f a) 0) μ :=
hf.neg.pos_part

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable.smul (c : 𝕜) {f : α → β}
  (hf : integrable f μ) : integrable (c • f) μ :=
⟨hf.ae_strongly_measurable.const_smul c, hf.has_finite_integral.smul c⟩

lemma integrable_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  integrable (c • f) μ ↔ integrable f μ :=
and_congr (ae_strongly_measurable_const_smul_iff₀ hc) (has_finite_integral_smul_iff hc f)

lemma integrable.smul_of_top_right {f : α → β} {φ : α → 𝕜}
  (hf : integrable f μ) (hφ : mem_ℒp φ ∞ μ) :
  integrable (φ • f) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact mem_ℒp.smul_of_top_right hf hφ }

lemma integrable.smul_of_top_left {f : α → β} {φ : α → 𝕜}
  (hφ : integrable φ μ) (hf : mem_ℒp f ∞ μ) :
  integrable (φ • f) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hφ ⊢, exact mem_ℒp.smul_of_top_left hf hφ }

lemma integrable.smul_const {f : α → 𝕜} (hf : integrable f μ) (c : β) :
  integrable (λ x, f x • c) μ :=
hf.smul_of_top_left (mem_ℒp_top_const c)

end normed_space

section normed_space_over_complete_field
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [complete_space 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]

lemma integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
  integrable (λ x, f x • c) μ ↔ integrable f μ :=
begin
  simp_rw [integrable, ae_strongly_measurable_smul_const_iff hc, and.congr_right_iff,
    has_finite_integral, nnnorm_smul, ennreal.coe_mul],
  intro hf, rw [lintegral_mul_const' _ _ ennreal.coe_ne_top, ennreal.mul_lt_top_iff],
  have : ∀ x : ℝ≥0∞, x = 0 → x < ∞ := by simp,
  simp [hc, or_iff_left_of_imp (this _)]
end

end normed_space_over_complete_field

section is_R_or_C
variables {𝕜 : Type*} [is_R_or_C 𝕜] {f : α → 𝕜}

lemma integrable.const_mul {f : α → 𝕜} (h : integrable f μ) (c : 𝕜) :
  integrable (λ x, c * f x) μ :=
integrable.smul c h

lemma integrable.const_mul' {f : α → 𝕜} (h : integrable f μ) (c : 𝕜) :
  integrable ((λ (x : α), c) * f) μ :=
integrable.smul c h

lemma integrable.mul_const {f : α → 𝕜} (h : integrable f μ) (c : 𝕜) :
  integrable (λ x, f x * c) μ :=
by simp_rw [mul_comm, h.const_mul _]

lemma integrable.mul_const' {f : α → 𝕜} (h : integrable f μ) (c : 𝕜) :
  integrable (f * (λ (x : α), c)) μ :=
integrable.mul_const h c

lemma integrable.div_const {f : α → 𝕜} (h : integrable f μ) (c : 𝕜) :
  integrable (λ x, f x / c) μ :=
by simp_rw [div_eq_mul_inv, h.mul_const]

lemma integrable.bdd_mul' {f g : α → 𝕜} {c : ℝ} (hg : integrable g μ)
  (hf : ae_strongly_measurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
  integrable (λ x, f x * g x) μ :=
begin
  refine integrable.mono' (hg.norm.smul c) (hf.mul hg.1) _,
  filter_upwards [hf_bound] with x hx,
  rw [pi.smul_apply, smul_eq_mul],
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)),
end

lemma integrable.of_real {f : α → ℝ} (hf : integrable f μ) :
  integrable (λ x, (f x : 𝕜)) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.of_real }

lemma integrable.re_im_iff :
  integrable (λ x, is_R_or_C.re (f x)) μ ∧ integrable (λ x, is_R_or_C.im (f x)) μ ↔
  integrable f μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable, exact mem_ℒp_re_im_iff }

lemma integrable.re (hf : integrable f μ) : integrable (λ x, is_R_or_C.re (f x)) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.re, }

lemma integrable.im (hf : integrable f μ) : integrable (λ x, is_R_or_C.im (f x)) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.im, }

end is_R_or_C

section inner_product
variables {𝕜 E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] {f : α → E}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

lemma integrable.const_inner (c : E) (hf : integrable f μ) : integrable (λ x, ⟪c, f x⟫) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.const_inner c, }

lemma integrable.inner_const (hf : integrable f μ) (c : E) : integrable (λ x, ⟪f x, c⟫) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.inner_const c, }

end inner_product

section trim

variables {H : Type*} [normed_add_comm_group H] {m0 : measurable_space α} {μ' : measure α}
  {f : α → H}

lemma integrable.trim (hm : m ≤ m0) (hf_int : integrable f μ') (hf : strongly_measurable[m] f) :
  integrable f (μ'.trim hm) :=
begin
  refine ⟨hf.ae_strongly_measurable, _⟩,
  rw [has_finite_integral, lintegral_trim hm _],
  { exact hf_int.2, },
  { exact @strongly_measurable.ennnorm _ m _ _ f hf },
end

lemma integrable_of_integrable_trim (hm : m ≤ m0) (hf_int : integrable f (μ'.trim hm)) :
  integrable f μ' :=
begin
  obtain ⟨hf_meas_ae, hf⟩ := hf_int,
  refine ⟨ae_strongly_measurable_of_ae_strongly_measurable_trim hm hf_meas_ae, _⟩,
  rw has_finite_integral at hf ⊢,
  rwa lintegral_trim_ae hm _ at hf,
  exact ae_strongly_measurable.ennnorm hf_meas_ae
end

end trim

section sigma_finite

variables {E : Type*} {m0 : measurable_space α} [normed_add_comm_group E]

lemma integrable_of_forall_fin_meas_le' {μ : measure α} (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (C : ℝ≥0∞) (hC : C < ∞) {f : α → E} (hf_meas : ae_strongly_measurable f μ)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, ‖f x‖₊ ∂μ ≤ C) :
  integrable f μ :=
⟨hf_meas, (lintegral_le_of_forall_fin_meas_le' hm C hf_meas.ennnorm hf).trans_lt hC⟩

lemma integrable_of_forall_fin_meas_le [sigma_finite μ]
  (C : ℝ≥0∞) (hC : C < ∞) {f : α → E} (hf_meas : ae_strongly_measurable f μ)
  (hf : ∀ s : set α, measurable_set s → μ s ≠ ∞ → ∫⁻ x in s, ‖f x‖₊ ∂μ ≤ C) :
  integrable f μ :=
@integrable_of_forall_fin_meas_le' _ _ _ _ _ _ _ (by rwa trim_eq_self) C hC _ hf_meas hf

end sigma_finite

/-! ### The predicate `integrable` on measurable functions modulo a.e.-equality -/

namespace ae_eq_fun

section

/-- A class of almost everywhere equal functions is `integrable` if its function representative
is integrable. -/
def integrable (f : α →ₘ[μ] β) : Prop := integrable f μ

lemma integrable_mk {f : α → β} (hf : ae_strongly_measurable f μ ) :
  (integrable (mk f hf : α →ₘ[μ] β)) ↔ measure_theory.integrable f μ :=
begin
  simp [integrable],
  apply integrable_congr,
  exact coe_fn_mk f hf
end

lemma integrable_coe_fn {f : α →ₘ[μ] β} : (measure_theory.integrable f μ) ↔ integrable f :=
by rw [← integrable_mk, mk_coe_fn]

lemma integrable_zero : integrable (0 : α →ₘ[μ] β) :=
(integrable_zero α β μ).congr (coe_fn_mk _ _).symm

end

section

lemma integrable.neg {f : α →ₘ[μ] β} : integrable f → integrable (-f) :=
induction_on f $ λ f hfm hfi, (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section

lemma integrable_iff_mem_L1 {f : α →ₘ[μ] β} : integrable f ↔ f ∈ (α →₁[μ] β) :=
by rw [← integrable_coe_fn, ← mem_ℒp_one_iff_integrable, Lp.mem_Lp_iff_mem_ℒp]

lemma integrable.add {f g : α →ₘ[μ] β} : integrable f → integrable g → integrable (f + g) :=
begin
  refine induction_on₂ f g (λ f hf g hg hfi hgi, _),
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢,
  exact hfi.add hgi
end

lemma integrable.sub {f g : α →ₘ[μ] β} (hf : integrable f) (hg : integrable g) :
  integrable (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : integrable f → integrable (c • f) :=
induction_on f $ λ f hfm hfi, (integrable_mk _).2 $ ((integrable_mk hfm).1 hfi).smul _

end normed_space

end

end ae_eq_fun

namespace L1

lemma integrable_coe_fn (f : α →₁[μ] β) :
  integrable f μ :=
by { rw ← mem_ℒp_one_iff_integrable, exact Lp.mem_ℒp f }

lemma has_finite_integral_coe_fn (f : α →₁[μ] β) :
  has_finite_integral f μ :=
(integrable_coe_fn f).has_finite_integral

lemma strongly_measurable_coe_fn (f : α →₁[μ] β) : strongly_measurable f :=
Lp.strongly_measurable f

lemma measurable_coe_fn [measurable_space β] [borel_space β] (f : α →₁[μ] β) :
  measurable f :=
(Lp.strongly_measurable f).measurable

lemma ae_strongly_measurable_coe_fn (f : α →₁[μ] β) : ae_strongly_measurable f μ :=
Lp.ae_strongly_measurable f

lemma ae_measurable_coe_fn [measurable_space β] [borel_space β] (f : α →₁[μ] β) :
  ae_measurable f μ :=
(Lp.strongly_measurable f).measurable.ae_measurable

lemma edist_def (f g : α →₁[μ] β) :
  edist f g = ∫⁻ a, edist (f a) (g a) ∂μ :=
by { simp [Lp.edist_def, snorm, snorm'], simp [edist_eq_coe_nnnorm_sub] }

lemma dist_def (f g : α →₁[μ] β) :
  dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).to_real :=
by { simp [Lp.dist_def, snorm, snorm'], simp [edist_eq_coe_nnnorm_sub] }

lemma norm_def (f : α →₁[μ] β) :
  ‖f‖ = (∫⁻ a, ‖f a‖₊ ∂μ).to_real :=
by { simp [Lp.norm_def, snorm, snorm'] }

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
lemma norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  ‖f - g‖ = (∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ∂μ).to_real :=
begin
  rw [norm_def],
  congr' 1,
  rw lintegral_congr_ae,
  filter_upwards [Lp.coe_fn_sub f g] with _ ha,
  simp only [ha, pi.sub_apply],
end

lemma of_real_norm_eq_lintegral (f : α →₁[μ] β) :
  ennreal.of_real ‖f‖ = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂μ :=
by { rw [norm_def, ennreal.of_real_to_real], exact ne_of_lt (has_finite_integral_coe_fn f) }

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `of_real_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
lemma of_real_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  ennreal.of_real ‖f - g‖ = ∫⁻ x, (‖f x - g x‖₊ : ℝ≥0∞) ∂μ :=
begin
  simp_rw [of_real_norm_eq_lintegral, ← edist_eq_coe_nnnorm],
  apply lintegral_congr_ae,
  filter_upwards [Lp.coe_fn_sub f g] with _ ha,
  simp only [ha, pi.sub_apply],
end

end L1

namespace integrable

/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `L1 β 1 μ`. -/
def to_L1 (f : α → β) (hf : integrable f μ) : α →₁[μ] β :=
(mem_ℒp_one_iff_integrable.2 hf).to_Lp f

@[simp] lemma to_L1_coe_fn (f : α →₁[μ] β) (hf : integrable f μ) : hf.to_L1 f = f :=
by simp [integrable.to_L1]

lemma coe_fn_to_L1 {f : α → β} (hf : integrable f μ) : hf.to_L1 f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

@[simp] lemma to_L1_zero (h : integrable (0 : α → β) μ) : h.to_L1 0 = 0 := rfl

@[simp] lemma to_L1_eq_mk (f : α → β) (hf : integrable f μ) :
  (hf.to_L1 f : α →ₘ[μ] β) = ae_eq_fun.mk f hf.ae_strongly_measurable :=
rfl

@[simp] lemma to_L1_eq_to_L1_iff (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 f hf = to_L1 g hg ↔ f =ᵐ[μ] g :=
mem_ℒp.to_Lp_eq_to_Lp_iff _ _

lemma to_L1_add (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 (f + g) (hf.add hg) = to_L1 f hf + to_L1 g hg := rfl

lemma to_L1_neg (f : α → β) (hf : integrable f μ) :
  to_L1 (- f) (integrable.neg hf) = - to_L1 f hf := rfl

lemma to_L1_sub (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 (f - g) (hf.sub hg) = to_L1 f hf - to_L1 g hg := rfl

lemma norm_to_L1 (f : α → β) (hf : integrable f μ) :
  ‖hf.to_L1 f‖ = ennreal.to_real (∫⁻ a, edist (f a) 0 ∂μ) :=
by { simp [to_L1, snorm, snorm'], simp [edist_eq_coe_nnnorm] }

lemma norm_to_L1_eq_lintegral_norm (f : α → β) (hf : integrable f μ) :
  ‖hf.to_L1 f‖ = ennreal.to_real (∫⁻ a, (ennreal.of_real ‖f a‖) ∂μ) :=
by { rw [norm_to_L1, lintegral_norm_eq_lintegral_edist] }

@[simp] lemma edist_to_L1_to_L1 (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  edist (hf.to_L1 f) (hg.to_L1 g) = ∫⁻ a, edist (f a) (g a) ∂μ :=
by { simp [integrable.to_L1, snorm, snorm'], simp [edist_eq_coe_nnnorm_sub] }

@[simp] lemma edist_to_L1_zero (f : α → β) (hf : integrable f μ) :
  edist (hf.to_L1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ :=
by { simp [integrable.to_L1, snorm, snorm'], simp [edist_eq_coe_nnnorm] }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma to_L1_smul (f : α → β) (hf : integrable f μ) (k : 𝕜) :
  to_L1 (λ a, k • f a) (hf.smul k) = k • to_L1 f hf := rfl

lemma to_L1_smul' (f : α → β) (hf : integrable f μ) (k : 𝕜) :
  to_L1 (k • f) (hf.smul k) = k • to_L1 f hf := rfl

end integrable

end measure_theory

open measure_theory

variables {E : Type*} [normed_add_comm_group E]
          {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]
          {H : Type*} [normed_add_comm_group H] [normed_space 𝕜 H]

lemma measure_theory.integrable.apply_continuous_linear_map {φ : α → H →L[𝕜] E}
  (φ_int : integrable φ μ) (v : H) : integrable (λ a, φ a v) μ :=
(φ_int.norm.mul_const ‖v‖).mono' (φ_int.ae_strongly_measurable.apply_continuous_linear_map v)
  (eventually_of_forall $ λ a, (φ a).le_op_norm v)

lemma continuous_linear_map.integrable_comp {φ : α → H} (L : H →L[𝕜] E)
  (φ_int : integrable φ μ) : integrable (λ (a : α), L (φ a)) μ :=
((integrable.norm φ_int).const_mul ‖L‖).mono'
  (L.continuous.comp_ae_strongly_measurable φ_int.ae_strongly_measurable)
  (eventually_of_forall $ λ a, L.le_op_norm (φ a))

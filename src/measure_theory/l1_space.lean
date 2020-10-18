/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import measure_theory.ae_eq_fun

/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

In the second part, the space `L¹` of equivalence classes of integrable functions under the relation
of being almost everywhere equal is defined as a subspace of the space `L⁰`. See the file
`src/measure_theory/ae_eq_fun.lean` for information on `L⁰` space.

## Notation

* `α →₁ β` is the type of `L¹` space, where `α` is a `measure_space` and `β` is a `normed_group`
  with a `second_countable_topology`. `f : α →ₘ β` is a "function" in `L¹`. In comments, `[f]` is
  also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_group`.
  Then `has_finite_integral f` means `(∫⁻ a, nnnorm (f a)) < ⊤`.

* If `β` is moreover a `measurable_space` then `f` is called `integrable` if
  `f` is `measurable` and `has_finite_integral f` holds.

* The space `L¹` is defined as a subspace of `L⁰` :
  An `ae_eq_fun` `[f] : α →ₘ β` is in the space `L¹` if `edist [f] 0 < ⊤`, which means
  `(∫⁻ a, edist (f a) 0) < ⊤` if we expand the definition of `edist` in `L⁰`.

## Main statements

`L¹`, as a subspace, inherits most of the structures of `L⁰`.

## Implementation notes

Maybe `integrable f` should be mean `(∫⁻ a, edist (f a) 0) < ⊤`, so that `integrable` and
`ae_eq_fun.integrable` are more aligned. But in the end one can use the lemma
`lintegral_nnnorm_eq_lintegral_edist : (∫⁻ a, nnnorm (f a)) = (∫⁻ a, edist (f a) 0)` to switch the
two forms.

To prove something for an arbitrary integrable + measurable function, a useful theorem is
`integrable.induction` in the file `set_integral`.

## Tags

integrable, function space, l1

-/

noncomputable theory
open_locale classical topological_space big_operators

open set filter topological_space ennreal emetric measure_theory

variables {α β γ δ : Type*} [measurable_space α] {μ ν : measure α}
variables [normed_group β]
variables [normed_group γ]

namespace measure_theory

/-! ### Some results about the Lebesgue integral involving a normed group -/

lemma lintegral_nnnorm_eq_lintegral_edist (f : α → β) :
  ∫⁻ a, nnnorm (f a) ∂μ = ∫⁻ a, edist (f a) 0 ∂μ :=
by simp only [edist_eq_coe_nnnorm]

lemma lintegral_norm_eq_lintegral_edist (f : α → β) :
  ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ = ∫⁻ a, edist (f a) 0 ∂μ :=
by simp only [of_real_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm]

lemma lintegral_edist_triangle [second_countable_topology β] [measurable_space β]
  [opens_measurable_space β] {f g h : α → β}
  (hf : measurable f) (hg : measurable g) (hh : measurable h) :
  ∫⁻ a, edist (f a) (g a) ∂μ ≤ ∫⁻ a, edist (f a) (h a) ∂μ + ∫⁻ a, edist (g a) (h a) ∂μ :=
begin
  rw ← lintegral_add (hf.edist hh) (hg.edist hh),
  refine lintegral_mono (λ a, _),
  apply edist_triangle_right
end

lemma lintegral_nnnorm_zero : ∫⁻ a : α, nnnorm (0 : β) ∂μ = 0 := by simp

lemma lintegral_nnnorm_add [measurable_space β] [opens_measurable_space β]
  [measurable_space γ] [opens_measurable_space γ]
  {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g) :
  ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ = ∫⁻ a, nnnorm (f a) ∂μ + ∫⁻ a, nnnorm (g a) ∂μ :=
lintegral_add hf.ennnorm hg.ennnorm

lemma lintegral_nnnorm_neg {f : α → β} :
  ∫⁻ a, nnnorm ((-f) a) ∂μ = ∫⁻ a, nnnorm (f a) ∂μ :=
by simp only [pi.neg_apply, nnnorm_neg]

/-! ### The predicate `has_finite_integral` -/

/-- `has_finite_integral f μ` means that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `has_finite_integral f` means `has_finite_integral f volume`. -/
def has_finite_integral (f : α → β) (μ : measure α . volume_tac) : Prop :=
∫⁻ a, nnnorm (f a) ∂μ < ⊤

lemma has_finite_integral_iff_norm (f : α → β) :
  has_finite_integral f μ ↔ ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ < ⊤ :=
by simp only [has_finite_integral, of_real_norm_eq_coe_nnnorm]

lemma has_finite_integral_iff_edist (f : α → β) :
  has_finite_integral f μ ↔ ∫⁻ a, edist (f a) 0 ∂μ < ⊤ :=
by simp only [has_finite_integral_iff_norm, edist_dist, dist_zero_right]

lemma has_finite_integral_iff_of_real {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
  has_finite_integral f μ ↔ ∫⁻ a, ennreal.of_real (f a) ∂μ < ⊤ :=
have lintegral_eq : ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ = ∫⁻ a, ennreal.of_real (f a) ∂μ :=
begin
  refine lintegral_congr_ae (h.mono $ λ a h, _),
  rwa [real.norm_eq_abs, abs_of_nonneg]
end,
by rw [has_finite_integral_iff_norm, lintegral_eq]

lemma has_finite_integral.mono {f : α → β} {g : α → γ} (hg : has_finite_integral g μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) : has_finite_integral f μ :=
begin
  simp only [has_finite_integral_iff_norm] at *,
  calc ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ ≤ ∫⁻ (a : α), (ennreal.of_real ∥g a∥) ∂μ :
    lintegral_mono_ae (h.mono $ assume a h, of_real_le_of_real h)
    ... < ⊤ : hg
end

lemma has_finite_integral.mono' {f : α → β} {g : α → ℝ} (hg : has_finite_integral g μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ g a) : has_finite_integral f μ :=
hg.mono $ h.mono $ λ x hx, le_trans hx (le_abs_self _)

lemma has_finite_integral.congr' {f : α → β} {g : α → γ} (hf : has_finite_integral f μ)
  (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) :
  has_finite_integral g μ :=
hf.mono $ eventually_eq.le $ eventually_eq.symm h

lemma has_finite_integral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
⟨λ hf, hf.congr' h, λ hg, hg.congr' $ eventually_eq.symm h⟩

lemma has_finite_integral.congr {f g : α → β} (hf : has_finite_integral f μ) (h : f =ᵐ[μ] g) :
  has_finite_integral g μ :=
hf.congr' $ h.fun_comp norm

lemma has_finite_integral_congr {f g : α → β} (h : f =ᵐ[μ] g) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
has_finite_integral_congr' $ h.fun_comp norm

lemma has_finite_integral_const_iff {c : β} :
  has_finite_integral (λ x : α, c) μ ↔ c = 0 ∨ μ univ < ⊤ :=
begin
  simp only [has_finite_integral, lintegral_const],
  by_cases hc : c = 0,
  { simp [hc] },
  { simp only [hc, false_or],
    refine ⟨λ h, _, λ h, mul_lt_top coe_lt_top h⟩,
    replace h := mul_lt_top (@coe_lt_top $ (nnnorm c)⁻¹) h,
    rwa [← mul_assoc, ← coe_mul, _root_.inv_mul_cancel, coe_one, one_mul] at h,
    rwa [ne.def, nnnorm_eq_zero] }
end

lemma has_finite_integral_const [finite_measure μ] (c : β) : has_finite_integral (λ x : α, c) μ :=
has_finite_integral_const_iff.2 (or.inr $ measure_lt_top _ _)

lemma has_finite_integral_of_bounded [finite_measure μ] {f : α → β} {C : ℝ}
  (hC : ∀ᵐ a ∂μ, ∥f a∥ ≤ C) : has_finite_integral f μ :=
(has_finite_integral_const C).mono' hC

lemma has_finite_integral.mono_measure {f : α → β} (h : has_finite_integral f ν) (hμ : μ ≤ ν) :
  has_finite_integral f μ :=
lt_of_le_of_lt (lintegral_mono' hμ (le_refl _)) h

lemma has_finite_integral.add_measure {f : α → β} (hμ : has_finite_integral f μ)
  (hν : has_finite_integral f ν) : has_finite_integral f (μ + ν) :=
begin
  simp only [has_finite_integral, lintegral_add_measure] at *,
  exact add_lt_top.2 ⟨hμ, hν⟩
end

lemma has_finite_integral.left_of_add_measure {f : α → β} (h : has_finite_integral f (μ + ν)) :
  has_finite_integral f μ :=
h.mono_measure $ measure.le_add_right $ le_refl _

lemma has_finite_integral.right_of_add_measure {f : α → β} (h : has_finite_integral f (μ + ν)) :
  has_finite_integral f ν :=
h.mono_measure $ measure.le_add_left $ le_refl _

@[simp] lemma has_finite_integral_add_measure {f : α → β} :
  has_finite_integral f (μ + ν) ↔ has_finite_integral f μ ∧ has_finite_integral f ν :=
⟨λ h, ⟨h.left_of_add_measure, h.right_of_add_measure⟩, λ h, h.1.add_measure h.2⟩

lemma has_finite_integral.smul_measure {f : α → β} (h : has_finite_integral f μ) {c : ennreal}
  (hc : c < ⊤) : has_finite_integral f (c • μ) :=
begin
  simp only [has_finite_integral, lintegral_smul_measure] at *,
  exact mul_lt_top hc h
end

@[simp] lemma has_finite_integral_zero_measure (f : α → β) : has_finite_integral f 0 :=
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
  has_finite_integral (λa, ∥f a∥) μ :=
have eq : (λa, (nnnorm ∥f a∥ : ennreal)) = λa, (nnnorm (f a) : ennreal),
  by { funext, rw nnnorm_norm },
by { rwa [has_finite_integral, eq] }

lemma has_finite_integral_norm_iff (f : α → β) :
  has_finite_integral (λa, ∥f a∥) μ ↔ has_finite_integral f μ :=
has_finite_integral_congr' $ eventually_of_forall $ λ x, norm_norm (f x)

section dominated_convergence

variables {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

lemma all_ae_of_real_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a) :
  ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ∥F n a∥ ≤ ennreal.of_real (bound a) :=
λn, (h n).mono $ λ a h, ennreal.of_real_le_of_real h

lemma all_ae_tendsto_of_real_norm (h : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top $ 𝓝 $ f a) :
  ∀ᵐ a ∂μ, tendsto (λn, ennreal.of_real ∥F n a∥) at_top $ 𝓝 $ ennreal.of_real ∥f a∥ :=
h.mono $
  λ a h, tendsto_of_real $ tendsto.comp (continuous.tendsto continuous_norm _) h

lemma all_ae_of_real_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  ∀ᵐ a ∂μ, ennreal.of_real ∥f a∥ ≤ ennreal.of_real (bound a) :=
begin
  have F_le_bound := all_ae_of_real_F_le_bound h_bound,
  rw ← ae_all_iff at F_le_bound,
  apply F_le_bound.mp ((all_ae_tendsto_of_real_norm h_lim).mono _),
  assume a tendsto_norm F_le_bound,
  exact le_of_tendsto' tendsto_norm (F_le_bound)
end

lemma has_finite_integral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (bound_has_finite_integral : has_finite_integral bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  has_finite_integral f μ :=
/- `∥F n a∥ ≤ bound a` and `∥F n a∥ --> ∥f a∥` implies `∥f a∥ ≤ bound a`,
  and so `∫ ∥f∥ ≤ ∫ bound < ⊤` since `bound` is has_finite_integral -/
begin
  rw has_finite_integral_iff_norm,
  calc ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ ≤ ∫⁻ a, ennreal.of_real (bound a) ∂μ :
    lintegral_mono_ae $ all_ae_of_real_f_le_bound h_bound h_lim
    ... < ⊤ :
    begin
      rw ← has_finite_integral_iff_of_real,
      { exact bound_has_finite_integral },
      exact (h_bound 0).mono (λ a h, le_trans (norm_nonneg _) h)
    end
end

lemma tendsto_lintegral_norm_of_dominated_convergence [measurable_space β]
  [borel_space β] [second_countable_topology β]
  {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (F_measurable : ∀ n, measurable (F n))
  (f_measurable : measurable f)
  (bound_has_finite_integral : has_finite_integral bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, (ennreal.of_real ∥F n a - f a∥) ∂μ) at_top (𝓝 0) :=
let b := λa, 2 * ennreal.of_real (bound a) in
/- `∥F n a∥ ≤ bound a` and `F n a --> f a` implies `∥f a∥ ≤ bound a`, and thus by the
  triangle inequality, have `∥F n a - f a∥ ≤ 2 * (bound a). -/
have hb : ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ∥F n a - f a∥ ≤ b a,
begin
  assume n,
  filter_upwards [all_ae_of_real_F_le_bound h_bound n, all_ae_of_real_f_le_bound h_bound h_lim],
  assume a h₁ h₂,
  calc ennreal.of_real ∥F n a - f a∥ ≤ (ennreal.of_real ∥F n a∥) + (ennreal.of_real ∥f a∥) :
  begin
    rw [← ennreal.of_real_add],
    apply of_real_le_of_real,
    { apply norm_sub_le }, { exact norm_nonneg _ }, { exact norm_nonneg _ }
  end
    ... ≤ (ennreal.of_real (bound a)) + (ennreal.of_real (bound a)) : add_le_add h₁ h₂
    ... = b a : by rw ← two_mul
end,
/- On the other hand, `F n a --> f a` implies that `∥F n a - f a∥ --> 0`  -/
have h : ∀ᵐ a ∂μ, tendsto (λ n, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 0),
begin
  rw ← ennreal.of_real_zero,
  refine h_lim.mono (λ a h, (continuous_of_real.tendsto _).comp _),
  rwa ← tendsto_iff_norm_tendsto_zero
end,
/- Therefore, by the dominated convergence theorem for nonnegative integration, have
  ` ∫ ∥f a - F n a∥ --> 0 ` -/
begin
  suffices h : tendsto (λn, ∫⁻ a, (ennreal.of_real ∥F n a - f a∥) ∂μ) at_top (𝓝 (∫⁻ (a:α), 0 ∂μ)),
  { rwa lintegral_zero at h },
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence _ _ hb _ _,
  -- Show `λa, ∥f a - F n a∥` is measurable for all `n`
  { exact λn, measurable_of_real.comp ((F_measurable n).sub f_measurable).norm },
  -- Show `2 * bound` is has_finite_integral
  { rw has_finite_integral_iff_of_real at bound_has_finite_integral,
    { calc ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ennreal.of_real (bound a) ∂μ :
        by { rw lintegral_const_mul', exact coe_ne_top }
        ... < ⊤ : mul_lt_top (coe_lt_top) bound_has_finite_integral },
    filter_upwards [h_bound 0] λ a h, le_trans (norm_nonneg _) h },
  -- Show `∥f a - F n a∥ --> 0`
  { exact h }
end

end dominated_convergence

section pos_part
/-! Lemmas used for defining the positive part of a `L¹` function -/

lemma has_finite_integral.max_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (λa, max (f a) 0) μ :=
hf.mono $ eventually_of_forall $ λ x, by simp [real.norm_eq_abs, abs_le, abs_nonneg, le_abs_self]

lemma has_finite_integral.min_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (λa, min (f a) 0) μ :=
hf.mono $ eventually_of_forall $ λ x,
  by simp [real.norm_eq_abs, abs_le, abs_nonneg, neg_le, neg_le_abs_self]

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma has_finite_integral.smul (c : 𝕜) {f : α → β} : has_finite_integral f μ →
  has_finite_integral (c • f) μ :=
begin
  simp only [has_finite_integral], assume hfi,
  calc
    ∫⁻ (a : α), nnnorm (c • f a) ∂μ = ∫⁻ (a : α), (nnnorm c) * nnnorm (f a) ∂μ :
      by simp only [nnnorm_smul, ennreal.coe_mul]
    ... < ⊤ :
    begin
      rw lintegral_const_mul',
      exacts [mul_lt_top coe_lt_top hfi, coe_ne_top]
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

variables [measurable_space β] [measurable_space γ] [measurable_space δ]

/-- `integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `integrable f` means `integrable f volume`. -/
def integrable (f : α → β) (μ : measure α . volume_tac) : Prop :=
measurable f ∧ has_finite_integral f μ

lemma integrable.measurable {f : α → β} (hf : integrable f μ) : measurable f := hf.1
lemma integrable.has_finite_integral {f : α → β} (hf : integrable f μ) : has_finite_integral f μ :=
hf.2

lemma integrable.mono {f : α → β} {g : α → γ} (hg : integrable g μ) (hf : measurable f)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) : integrable f μ :=
⟨hf, hg.has_finite_integral.mono h⟩

lemma integrable.mono' {f : α → β} {g : α → ℝ} (hg : integrable g μ) (hf : measurable f)
  (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ g a) : integrable f μ :=
⟨hf, hg.has_finite_integral.mono' h⟩

lemma integrable.congr' {f : α → β} {g : α → γ} (hf : integrable f μ) (hg : measurable g)
  (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) : integrable g μ :=
⟨hg, hf.has_finite_integral.congr' h⟩

lemma integrable_congr' {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g)
  (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) : integrable f μ ↔ integrable g μ :=
⟨λ h2f, h2f.congr' hg h, λ h2g, h2g.congr' hf $ eventually_eq.symm h⟩

lemma integrable.congr {f g : α → β} (hf : integrable f μ) (hg : measurable g) (h : f =ᵐ[μ] g) :
  integrable g μ :=
hf.congr' hg $ h.fun_comp norm

lemma integrable_congr {f g : α → β} (hf : measurable f) (hg : measurable g) (h : f =ᵐ[μ] g) :
  integrable f μ ↔ integrable g μ :=
integrable_congr' hf hg $ h.fun_comp norm

lemma integrable_const_iff {c : β} : integrable (λ x : α, c) μ ↔ c = 0 ∨ μ univ < ⊤ :=
by rw [integrable, and_iff_right measurable_const, has_finite_integral_const_iff]

lemma integrable_const [finite_measure μ] (c : β) : integrable (λ x : α, c) μ :=
integrable_const_iff.2 $ or.inr $ measure_lt_top _ _

lemma integrable.mono_measure {f : α → β} (h : integrable f ν) (hμ : μ ≤ ν) : integrable f μ :=
⟨h.measurable, h.has_finite_integral.mono_measure hμ⟩

lemma integrable.add_measure {f : α → β} (hμ : integrable f μ) (hν : integrable f ν) :
  integrable f (μ + ν) :=
⟨hμ.measurable, hμ.has_finite_integral.add_measure hν.has_finite_integral⟩

lemma integrable.left_of_add_measure {f : α → β} (h : integrable f (μ + ν)) : integrable f μ :=
h.mono_measure $ measure.le_add_right $ le_refl _

lemma integrable.right_of_add_measure {f : α → β} (h : integrable f (μ + ν)) : integrable f ν :=
h.mono_measure $ measure.le_add_left $ le_refl _

@[simp] lemma integrable_add_measure {f : α → β} :
  integrable f (μ + ν) ↔ integrable f μ ∧ integrable f ν :=
⟨λ h, ⟨h.left_of_add_measure, h.right_of_add_measure⟩, λ h, h.1.add_measure h.2⟩

lemma integrable.smul_measure {f : α → β} (h : integrable f μ) {c : ennreal} (hc : c < ⊤) :
  integrable f (c • μ) :=
⟨h.measurable, h.has_finite_integral.smul_measure hc⟩

lemma integrable_map_measure [opens_measurable_space β] {f : α → δ} {g : δ → β}
  (hf : measurable f) (hg : measurable g) :
  integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
by { simp only [integrable, has_finite_integral, lintegral_map hg.ennnorm hf, hf, hg, hg.comp hf] }

lemma lintegral_edist_lt_top [second_countable_topology β] [opens_measurable_space β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) :
  ∫⁻ a, edist (f a) (g a) ∂μ < ⊤ :=
lt_of_le_of_lt
  (lintegral_edist_triangle hf.measurable hg.measurable
    (measurable_const : measurable (λa, (0 : β))))
  (ennreal.add_lt_top.2 $ by { simp_rw ← has_finite_integral_iff_edist,
                               exact ⟨hf.has_finite_integral, hg.has_finite_integral⟩ })


variables (α β μ)
@[simp] lemma integrable_zero : integrable (λ _, (0 : β)) μ :=
by simp [integrable, measurable_const]
variables {α β μ}

lemma integrable.add' [opens_measurable_space β] {f g : α → β} (hf : integrable f μ)
  (hg : integrable g μ) :
  has_finite_integral (f + g) μ :=
calc ∫⁻ a, nnnorm (f a + g a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ :
  lintegral_mono (λ a, by exact_mod_cast nnnorm_add_le _ _)
... = _ : lintegral_nnnorm_add hf.measurable hg.measurable
... < ⊤ : add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩

lemma integrable.add [borel_space β] [second_countable_topology β]
  {f g : α → β} (hf : integrable f μ) (hg : integrable g μ) : integrable (f + g) μ :=
⟨hf.measurable.add hg.measurable, hf.add' hg⟩

lemma integrable_finset_sum {ι} [borel_space β] [second_countable_topology β] (s : finset ι)
  {f : ι → α → β} (hf : ∀ i, integrable (f i) μ) : integrable (λ a, ∑ i in s, f i a) μ :=
begin
  refine finset.induction_on s _ _,
  { simp only [finset.sum_empty, integrable_zero] },
  { assume i s his ih, simp only [his, finset.sum_insert, not_false_iff],
    exact (hf _).add ih }
end

lemma integrable.neg [borel_space β] {f : α → β} (hf : integrable f μ) : integrable (-f) μ :=
⟨hf.measurable.neg, hf.has_finite_integral.neg⟩

@[simp] lemma integrable_neg_iff [borel_space β] {f : α → β} : integrable (-f) μ ↔ integrable f μ :=
⟨λ h, neg_neg f ▸ h.neg, integrable.neg⟩

lemma integrable.sub' [opens_measurable_space β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) : has_finite_integral (f - g) μ :=
calc ∫⁻ a, nnnorm (f a - g a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (-g a) ∂μ :
  lintegral_mono (assume a, by exact_mod_cast nnnorm_add_le _ _ )
... = _ :
  by { simp only [nnnorm_neg], exact lintegral_nnnorm_add hf.measurable hg.measurable }
... < ⊤ : add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩

lemma integrable.sub [borel_space β] [second_countable_topology β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) : integrable (f - g) μ :=
hf.add hg.neg

lemma integrable.norm [opens_measurable_space β] {f : α → β} (hf : integrable f μ) :
  integrable (λa, ∥f a∥) μ :=
⟨hf.measurable.norm, hf.has_finite_integral.norm⟩

lemma integrable_norm_iff [opens_measurable_space β] {f : α → β} (hf : measurable f) :
  integrable (λa, ∥f a∥) μ ↔ integrable f μ :=
by simp_rw [integrable, and_iff_right hf, and_iff_right hf.norm, has_finite_integral_norm_iff]

lemma integrable.prod_mk [opens_measurable_space β] [opens_measurable_space γ] {f : α → β}
  {g : α → γ} (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ x, (f x, g x)) μ :=
⟨hf.measurable.prod_mk hg.measurable,
  (hf.norm.add' hg.norm).mono $ eventually_of_forall $ λ x,
  calc max ∥f x∥ ∥g x∥ ≤ ∥f x∥ + ∥g x∥   : max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
                 ... ≤ ∥(∥f x∥ + ∥g x∥)∥ : le_abs_self _⟩

section pos_part
/-! ### Lemmas used for defining the positive part of a `L¹` function -/

lemma integrable.max_zero {f : α → ℝ} (hf : integrable f μ) : integrable (λa, max (f a) 0) μ :=
⟨hf.measurable.max measurable_const, hf.has_finite_integral.max_zero⟩

lemma integrable.min_zero {f : α → ℝ} (hf : integrable f μ) : integrable (λa, min (f a) 0) μ :=
⟨hf.measurable.min measurable_const, hf.has_finite_integral.min_zero⟩

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable.smul [borel_space β] (c : 𝕜) {f : α → β}
  (hf : integrable f μ) : integrable (c • f) μ :=
⟨hf.measurable.const_smul c, hf.has_finite_integral.smul c⟩

lemma integrable_smul_iff [borel_space β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  integrable (c • f) μ ↔ integrable f μ :=
and_congr (measurable_const_smul_iff hc) (has_finite_integral_smul_iff hc f)

lemma integrable.const_mul {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, c * f x) μ :=
integrable.smul c h

lemma integrable.mul_const {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, f x * c) μ :=
by simp_rw [mul_comm, h.const_mul _]

end normed_space

section normed_space_over_complete_field
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] [measurable_space 𝕜]
variables [borel_space 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E]

lemma integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
  integrable (λ x, f x • c) μ ↔ integrable f μ :=
begin
  simp_rw [integrable, measurable_smul_const hc, and.congr_right_iff, has_finite_integral,
    nnnorm_smul, ennreal.coe_mul],
  intro hf, rw [lintegral_mul_const' _ _ ennreal.coe_ne_top, ennreal.mul_lt_top_iff],
  have : ∀ x : ennreal, x = 0 → x < ⊤ := by simp,
  simp [hc, or_iff_left_of_imp (this _)]
end
end normed_space_over_complete_field


variables [second_countable_topology β]

/-! ### The predicate `integrable` on measurable functions modulo a.e.-equality -/

namespace ae_eq_fun

section

variable [opens_measurable_space β]

/-- A class of almost everywhere equal functions is `integrable` if it has a finite distance to
  the origin. It means the same thing as the predicate `integrable` over functions. -/
def integrable (f : α →ₘ[μ] β) : Prop := f ∈ ball (0 : α →ₘ[μ] β) ⊤

lemma integrable_mk {f : α → β} (hf : measurable f) :
  (integrable (mk f hf : α →ₘ[μ] β)) ↔ measure_theory.integrable f μ :=
by simp [integrable, zero_def, edist_mk_mk', measure_theory.integrable, nndist_eq_nnnorm,
         has_finite_integral, hf]

lemma integrable_coe_fn {f : α →ₘ[μ] β} : (measure_theory.integrable f μ) ↔ integrable f :=
by rw [← integrable_mk, mk_coe_fn]

lemma integrable_zero : integrable (0 : α →ₘ[μ] β) := mem_ball_self coe_lt_top

end

section

variable [borel_space β]

lemma integrable.add {f g : α →ₘ[μ] β} : integrable f → integrable g → integrable (f + g) :=
begin
  refine induction_on₂ f g (λ f hf g hg hfi hgi, _),
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢,
  exact hfi.add hgi
end

lemma integrable.neg {f : α →ₘ[μ] β} : integrable f → integrable (-f) :=
induction_on f $ λ f hfm hfi, (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

lemma integrable.sub {f g : α →ₘ[μ] β} (hf : integrable f) (hg : integrable g) :
  integrable (f - g) :=
hf.add hg.neg

protected lemma is_add_subgroup : is_add_subgroup (ball (0 : α →ₘ[μ] β) ⊤) :=
{ zero_mem := integrable_zero,
  add_mem := λ _ _, integrable.add,
  neg_mem := λ _, integrable.neg }

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : integrable f → integrable (c • f) :=
induction_on f $ λ f hfm hfi, (integrable_mk _).2 $ ((integrable_mk hfm).1 hfi).smul _

end normed_space

end

end ae_eq_fun

/-! ### The `L¹` space of functions -/

variables (α β)
/-- The space of equivalence classes of integrable (and measurable) functions, where two integrable
    functions are equivalent if they agree almost everywhere, i.e., they differ on a set of measure
    `0`. -/
def l1 [opens_measurable_space β] (μ : measure α) : Type* :=
{f : α →ₘ[μ] β // f.integrable}

notation α ` →₁[`:25 μ `] ` β := l1 α β μ

variables {α β}

namespace l1
open ae_eq_fun
local attribute [instance] ae_eq_fun.is_add_subgroup

section

variable [opens_measurable_space β]

instance : has_coe (α →₁[μ] β) (α →ₘ[μ] β) := coe_subtype
instance : has_coe_to_fun (α →₁[μ] β) := ⟨λ f, α → β, λ f, ⇑(f : α →ₘ[μ] β)⟩

@[simp, norm_cast] lemma coe_coe (f : α →₁[μ] β) : ⇑(f : α →ₘ[μ] β) = f := rfl

protected lemma eq {f g : α →₁[μ] β} : (f : α →ₘ[μ] β) = (g : α →ₘ[μ] β) → f = g := subtype.eq
@[norm_cast] protected lemma eq_iff {f g : α →₁[μ] β} : (f : α →ₘ[μ] β) = (g : α →ₘ[μ] β) ↔ f = g :=
iff.intro (l1.eq) (congr_arg coe)

/- TODO : order structure of l1-/

/-- `L¹` space forms a `emetric_space`, with the emetric being inherited from almost everywhere
  functions, i.e., `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
instance : emetric_space (α →₁[μ] β) := subtype.emetric_space

/-- `L¹` space forms a `metric_space`, with the metric being inherited from almost everywhere
  functions, i.e., `edist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a))`. -/
instance : metric_space (α →₁[μ] β) := metric_space_emetric_ball 0 ⊤

end

variable [borel_space β]

instance : add_comm_group (α →₁[μ] β) := subtype.add_comm_group

instance : inhabited (α →₁[μ] β) := ⟨0⟩

@[simp, norm_cast] lemma coe_zero : ((0 : α →₁[μ] β) : α →ₘ[μ] β) = 0 := rfl
@[simp, norm_cast]
lemma coe_add (f g : α →₁[μ] β) : ((f + g : α →₁[μ] β) : α →ₘ[μ] β) = f + g := rfl
@[simp, norm_cast] lemma coe_neg (f : α →₁[μ] β) : ((-f : α →₁[μ] β) : α →ₘ[μ] β) = -f := rfl
@[simp, norm_cast]
lemma coe_sub (f g : α →₁[μ] β) : ((f - g : α →₁[μ] β) : α →ₘ[μ] β) = f - g := rfl

@[simp] lemma edist_eq (f g : α →₁[μ] β) : edist f g = edist (f : α →ₘ[μ] β) (g : α →ₘ[μ] β) := rfl

lemma dist_eq (f g : α →₁[μ] β) :
  dist f g = ennreal.to_real (edist (f : α →ₘ[μ] β) (g : α →ₘ[μ] β)) :=
rfl

/-- The norm on `L¹` space is defined to be `∥f∥ = ∫⁻ a, edist (f a) 0`. -/
instance : has_norm (α →₁[μ] β) := ⟨λ f, dist f 0⟩

lemma norm_eq (f : α →₁[μ] β) : ∥f∥ = ennreal.to_real (edist (f : α →ₘ[μ] β) 0) := rfl

instance : normed_group (α →₁[μ] β) := normed_group.of_add_dist (λ x, rfl) $ by
{ intros, simp only [dist_eq, coe_add], rw edist_add_right }

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

instance : has_scalar 𝕜 (α →₁[μ] β) := ⟨λ x f, ⟨x • (f : α →ₘ[μ] β), ae_eq_fun.integrable.smul f.2⟩⟩

@[simp, norm_cast] lemma coe_smul (c : 𝕜) (f : α →₁[μ] β) :
  ((c • f : α →₁[μ] β) : α →ₘ[μ] β) = c • (f : α →ₘ[μ] β) := rfl

instance : semimodule 𝕜 (α →₁[μ] β) :=
{ one_smul  := λf, l1.eq (by { simp only [coe_smul], exact one_smul _ _ }),
  mul_smul  := λx y f, l1.eq (by { simp only [coe_smul], exact mul_smul _ _ _ }),
  smul_add  := λx f g, l1.eq (by { simp only [coe_smul, coe_add], exact smul_add _ _ _ }),
  smul_zero := λx, l1.eq (by { simp only [coe_zero, coe_smul], exact smul_zero _ }),
  add_smul  := λx y f, l1.eq (by { simp only [coe_smul], exact add_smul _ _ _ }),
  zero_smul := λf, l1.eq (by { simp only [coe_smul], exact zero_smul _ _ }) }

instance : normed_space 𝕜 (α →₁[μ] β) :=
⟨ begin
    rintros x ⟨f, hf⟩,
    show ennreal.to_real (edist (x • f) 0) ≤ ∥x∥ * ennreal.to_real (edist f 0),
    rw [edist_smul, to_real_of_real_mul],
    exact norm_nonneg _
  end ⟩

end normed_space

section of_fun

/-- Construct the equivalence class `[f]` of a measurable and integrable function `f`. -/
def of_fun (f : α → β) (hf : integrable f μ) : (α →₁[μ] β) :=
⟨mk f hf.measurable, by { rw integrable_mk, exact hf }⟩

@[simp] lemma of_fun_eq_mk (f : α → β) (hf : integrable f μ) :
  (of_fun f hf : α →ₘ[μ] β) = mk f hf.measurable :=
rfl

lemma of_fun_eq_of_fun (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  of_fun f hf = of_fun g hg ↔ f =ᵐ[μ] g :=
by { rw ← l1.eq_iff, simp only [of_fun_eq_mk, mk_eq_mk] }

lemma of_fun_zero : of_fun (λ _, (0 : β)) (integrable_zero α β μ) = 0 := rfl

lemma of_fun_add (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  of_fun (f + g) (hf.add hg) = of_fun f hf + of_fun g hg :=
rfl

lemma of_fun_neg (f : α → β) (hf : integrable f μ) :
  of_fun (- f) (integrable.neg hf) = - of_fun f hf := rfl

lemma of_fun_sub (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  of_fun (f - g) (hf.sub hg) = of_fun f hf - of_fun g hg :=
rfl

lemma norm_of_fun (f : α → β) (hf : integrable f μ) :
  ∥ of_fun f hf ∥ = ennreal.to_real (∫⁻ a, edist (f a) 0 ∂μ) :=
rfl

lemma norm_of_fun_eq_lintegral_norm (f : α → β) (hf : integrable f μ) :
  ∥ of_fun f hf ∥ = ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :=
by { rw [norm_of_fun, lintegral_norm_eq_lintegral_edist] }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma of_fun_smul (f : α → β) (hf : integrable f μ) (k : 𝕜) :
  of_fun (λa, k • f a) (hf.smul k) = k • of_fun f hf := rfl

end of_fun

section to_fun

protected lemma measurable (f : α →₁[μ] β) : measurable f := f.1.measurable

lemma measurable_norm (f : α →₁[μ] β) : measurable (λ a, ∥f a∥) :=
f.measurable.norm

protected lemma integrable (f : α →₁[μ] β) : integrable ⇑f μ :=
integrable_coe_fn.2 f.2

protected lemma has_finite_integral (f : α →₁[μ] β) : has_finite_integral ⇑f μ :=
f.integrable.has_finite_integral

lemma integrable_norm (f : α →₁[μ] β) : integrable (λ a, ∥f a∥) μ :=
(integrable_norm_iff f.measurable).mpr f.integrable

lemma of_fun_to_fun (f : α →₁[μ] β) : of_fun f f.integrable = f :=
subtype.ext (f : α →ₘ[μ] β).mk_coe_fn

lemma mk_to_fun (f : α →₁[μ] β) : (mk f f.measurable : α →ₘ[μ] β) = f :=
by { rw ← of_fun_eq_mk, rw l1.eq_iff, exact of_fun_to_fun f }

lemma to_fun_of_fun (f : α → β) (hf : integrable f μ) : ⇑(of_fun f hf : α →₁[μ] β) =ᵐ[μ] f :=
coe_fn_mk f hf.measurable

variables (α β)
lemma zero_to_fun : ⇑(0 : α →₁[μ] β) =ᵐ[μ] 0 := ae_eq_fun.coe_fn_zero
variables {α β}

lemma add_to_fun (f g : α →₁[μ] β) : ⇑(f + g) =ᵐ[μ] f + g :=
ae_eq_fun.coe_fn_add _ _

lemma neg_to_fun (f : α →₁[μ] β) : ⇑(-f) =ᵐ[μ] -⇑f := ae_eq_fun.coe_fn_neg _

lemma sub_to_fun (f g : α →₁[μ] β) : ⇑(f - g) =ᵐ[μ] ⇑f - ⇑g :=
ae_eq_fun.coe_fn_sub _ _

lemma dist_to_fun (f g : α →₁[μ] β) : dist f g = ennreal.to_real (∫⁻ x, edist (f x) (g x) ∂μ) :=
by { simp only [← coe_coe, dist_eq, edist_eq_coe] }

lemma norm_eq_nnnorm_to_fun (f : α →₁[μ] β) : ∥f∥ = ennreal.to_real (∫⁻ a, nnnorm (f a) ∂μ) :=
by { rw [← coe_coe, lintegral_nnnorm_eq_lintegral_edist, ← edist_zero_eq_coe], refl }

lemma norm_eq_norm_to_fun (f : α →₁[μ] β) :
  ∥f∥ = ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :=
by { rw norm_eq_nnnorm_to_fun, congr, funext, rw of_real_norm_eq_coe_nnnorm }

lemma lintegral_edist_to_fun_lt_top (f g : α →₁[μ] β) : (∫⁻ a, edist (f a) (g a) ∂μ) < ⊤ :=
lintegral_edist_lt_top f.integrable g.integrable

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma smul_to_fun (c : 𝕜) (f : α →₁[μ] β) : ⇑(c • f) =ᵐ[μ] c • f :=
ae_eq_fun.coe_fn_smul _ _

lemma norm_eq_lintegral (f : α →₁[μ] β) : ∥f∥ = (∫⁻ x, (nnnorm (f x) : ennreal) ∂μ).to_real :=
by simp [l1.norm_eq, ae_eq_fun.edist_zero_eq_coe, ← edist_eq_coe_nnnorm]

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
lemma norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  ∥f - g∥ = (∫⁻ x, (nnnorm (f x - g x) : ennreal) ∂μ).to_real :=
begin
  simp_rw [l1.norm_eq, ae_eq_fun.edist_zero_eq_coe, ← edist_eq_coe_nnnorm],
  rw lintegral_congr_ae,
  refine (ae_eq_fun.coe_fn_sub (f : α →ₘ[μ] β) g).mp _,
  apply eventually_of_forall, intros x hx, simp [hx]
end

lemma of_real_norm_eq_lintegral (f : α →₁[μ] β) :
  ennreal.of_real ∥f∥ = ∫⁻ x, (nnnorm (f x) : ennreal) ∂μ :=
by { rw [norm_eq_lintegral, ennreal.of_real_to_real], rw [← ennreal.lt_top_iff_ne_top],
  exact f.has_finite_integral }

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `of_real_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
lemma of_real_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  ennreal.of_real ∥f - g∥ = ∫⁻ x, (nnnorm (f x - g x) : ennreal) ∂μ :=
begin
  simp_rw [of_real_norm_eq_lintegral, ← edist_eq_coe_nnnorm],
  apply lintegral_congr_ae,
  refine (ae_eq_fun.coe_fn_sub (f : α →ₘ[μ] β) g).mp _,
  apply eventually_of_forall, intros x hx, simp only [l1.coe_coe, pi.sub_apply] at hx,
  simp_rw [← hx, ← l1.coe_sub, l1.coe_coe]
end

end to_fun

section pos_part

/-- Positive part of a function in `L¹` space. -/
def pos_part (f : α →₁[μ] ℝ) : α →₁[μ] ℝ :=
⟨ae_eq_fun.pos_part f,
  begin
    rw [← ae_eq_fun.integrable_coe_fn, integrable_congr (ae_eq_fun.measurable _)
      (f.measurable.max measurable_const) (coe_fn_pos_part _)],
    exact f.integrable.max_zero
  end ⟩

/-- Negative part of a function in `L¹` space. -/
def neg_part (f : α →₁[μ] ℝ) : α →₁[μ] ℝ := pos_part (-f)

@[norm_cast]
lemma coe_pos_part (f : α →₁[μ] ℝ) : (f.pos_part : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part := rfl

lemma pos_part_to_fun (f : α →₁[μ] ℝ) : ⇑(pos_part f) =ᵐ[μ] λ a, max (f a) 0 :=
ae_eq_fun.coe_fn_pos_part _

lemma neg_part_to_fun_eq_max (f : α →₁[μ] ℝ) : ∀ᵐ a ∂μ, neg_part f a = max (- f a) 0 :=
begin
  rw neg_part,
  filter_upwards [pos_part_to_fun (-f), neg_to_fun f],
  simp only [mem_set_of_eq],
  assume a h₁ h₂,
  rw [h₁, h₂, pi.neg_apply]
end

lemma neg_part_to_fun_eq_min (f : α →₁[μ] ℝ) : ∀ᵐ a ∂μ, neg_part f a = - min (f a) 0 :=
(neg_part_to_fun_eq_max f).mono $ assume a h,
by rw [h, ← max_neg_neg, neg_zero]

lemma norm_le_norm_of_ae_le {f g : α →₁[μ] β} (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) : ∥f∥ ≤ ∥g∥ :=
begin
  simp only [l1.norm_eq_norm_to_fun],
  rw to_real_le_to_real,
  { apply lintegral_mono_ae,
    exact h.mono (λ a h, of_real_le_of_real h) },
  { rw [← lt_top_iff_ne_top, ← has_finite_integral_iff_norm], exact f.has_finite_integral },
  { rw [← lt_top_iff_ne_top, ← has_finite_integral_iff_norm], exact g.has_finite_integral }
end

lemma continuous_pos_part : continuous $ λf : α →₁[μ] ℝ, pos_part f :=
begin
  simp only [metric.continuous_iff],
  assume g ε hε,
  use ε, use hε,
  simp only [dist_eq_norm],
  assume f hfg,
  refine lt_of_le_of_lt (norm_le_norm_of_ae_le _) hfg,
  filter_upwards [l1.sub_to_fun f g, l1.sub_to_fun (pos_part f) (pos_part g),
    pos_part_to_fun f, pos_part_to_fun g],
  simp only [mem_set_of_eq],
  assume a h₁ h₂ h₃ h₄,
  simp only [real.norm_eq_abs, h₁, h₂, h₃, h₄, pi.sub_apply],
  exact abs_max_sub_max_le_abs _ _ _
end

lemma continuous_neg_part : continuous $ λf : α →₁[μ] ℝ, neg_part f :=
have eq : (λf : α →₁[μ] ℝ, neg_part f) = (λf : α →₁[μ] ℝ, pos_part (-f)) := rfl,
by { rw eq, exact continuous_pos_part.comp continuous_neg }

end pos_part

/- TODO: l1 is a complete space -/

end l1

end measure_theory
open measure_theory

lemma measurable.integrable_zero [measurable_space β] {f : α → β} (hf : measurable f) :
  integrable f 0 :=
⟨hf, has_finite_integral_zero_measure f⟩

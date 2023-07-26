/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation.condexp_L1

/-! # Conditional expectation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m0`) and a measurable space
structure `m` with `hm : m ≤ m0` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condexp_L1_clm` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `measure_theory.function.conditional_expectation.condexp_L2`, the two
next steps in `measure_theory.function.conditional_expectation.condexp_L1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condexp (m : measurable_space α) (μ : measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `strongly_measurable_condexp` : `condexp` is `m`-strongly-measurable.
* `set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s)` : if `m ≤ m0` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condexp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condexp` is function-valued, we also define `condexp_L1` with value in `L1` and a continuous
linear map `condexp_L1_clm` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condexp_of_forall_set_integral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condexp m μ f`.

## Tags

conditional expectation, conditional expected value

-/

open topological_space measure_theory.Lp filter
open_locale ennreal topology big_operators measure_theory

namespace measure_theory

variables {α F F' 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [normed_add_comm_group F] [normed_space 𝕜 F]
  -- F' for integrals on a Lp submodule
  [normed_add_comm_group F'] [normed_space 𝕜 F'] [normed_space ℝ F'] [complete_space F']

open_locale classical

variables {𝕜} {m m0 : measurable_space α} {μ : measure α} {f g : α → F'} {s : set α}

/-- Conditional expectation of a function. It is defined as 0 if any one of the following conditions
is true:
- `m` is not a sub-σ-algebra of `m0`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
@[irreducible]
noncomputable
def condexp (m : measurable_space α) {m0 : measurable_space α} (μ : measure α) (f : α → F') :
  α → F' :=
if hm : m ≤ m0
  then if h : sigma_finite (μ.trim hm) ∧ integrable f μ
    then if strongly_measurable[m] f
      then f
      else (@ae_strongly_measurable'_condexp_L1 _ _ _ _ _ m m0 μ hm h.1 _).mk
        (@condexp_L1 _ _ _ _ _ _ _ hm μ h.1 f)
    else 0
  else 0

-- We define notation `μ[f|m]` for the conditional expectation of `f` with respect to `m`.
localized "notation (name := measure_theory.condexp)
  μ `[` f `|` m `]` := measure_theory.condexp m μ f" in measure_theory

lemma condexp_of_not_le (hm_not : ¬ m ≤ m0) : μ[f|m] = 0 := by rw [condexp, dif_neg hm_not]

lemma condexp_of_not_sigma_finite (hm : m ≤ m0) (hμm_not : ¬ sigma_finite (μ.trim hm)) :
  μ[f|m] = 0 :=
by { rw [condexp, dif_pos hm, dif_neg], push_neg, exact λ h, absurd h hμm_not, }

lemma condexp_of_sigma_finite (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)] :
  μ[f|m] =
  if integrable f μ
    then if strongly_measurable[m] f
      then f else ae_strongly_measurable'_condexp_L1.mk (condexp_L1 hm μ f)
    else 0 :=
begin
  rw [condexp, dif_pos hm],
  simp only [hμm, ne.def, true_and],
  by_cases hf : integrable f μ,
  { rw [dif_pos hf, if_pos hf], },
  { rw [dif_neg hf, if_neg hf], },
end

lemma condexp_of_strongly_measurable (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  {f : α → F'} (hf : strongly_measurable[m] f) (hfi : integrable f μ) :
  μ[f|m] = f :=
by { rw [condexp_of_sigma_finite hm, if_pos hfi, if_pos hf], apply_instance, }

lemma condexp_const (hm : m ≤ m0) (c : F') [is_finite_measure μ] : μ[(λ x : α, c)|m] = λ _, c :=
condexp_of_strongly_measurable hm (@strongly_measurable_const _ _ m _ _) (integrable_const c)

lemma condexp_ae_eq_condexp_L1 (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  (f : α → F') : μ[f|m] =ᵐ[μ] condexp_L1 hm μ f :=
begin
  rw condexp_of_sigma_finite hm,
  by_cases hfi : integrable f μ,
  { rw if_pos hfi,
    by_cases hfm : strongly_measurable[m] f,
    { rw if_pos hfm,
      exact (condexp_L1_of_ae_strongly_measurable'
        (strongly_measurable.ae_strongly_measurable' hfm) hfi).symm, },
    { rw if_neg hfm,
      exact (ae_strongly_measurable'.ae_eq_mk ae_strongly_measurable'_condexp_L1).symm, }, },
  rw [if_neg hfi, condexp_L1_undef hfi],
  exact (coe_fn_zero _ _ _).symm,
end

lemma condexp_ae_eq_condexp_L1_clm (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hf : integrable f μ) :
  μ[f|m] =ᵐ[μ] condexp_L1_clm hm μ (hf.to_L1 f) :=
begin
  refine (condexp_ae_eq_condexp_L1 hm f).trans (eventually_of_forall (λ x, _)),
  rw condexp_L1_eq hf,
end

lemma condexp_undef (hf : ¬ integrable f μ) : μ[f|m] = 0 :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  rw [condexp_of_sigma_finite, if_neg hf],
end

@[simp] lemma condexp_zero : μ[(0 : α → F')|m] = 0 :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact condexp_of_strongly_measurable hm (@strongly_measurable_zero _ _ m _ _)
    (integrable_zero _ _ _),
end

lemma strongly_measurable_condexp : strongly_measurable[m] (μ[f|m]) :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, exact strongly_measurable_zero, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, exact strongly_measurable_zero, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  rw condexp_of_sigma_finite hm,
  swap, { apply_instance, },
  split_ifs with hfi hfm,
  { exact hfm, },
  { exact ae_strongly_measurable'.strongly_measurable_mk _, },
  { exact strongly_measurable_zero, },
end

lemma condexp_congr_ae (h : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (condexp_ae_eq_condexp_L1 hm f).trans
    (filter.eventually_eq.trans (by rw condexp_L1_congr_ae hm h)
    (condexp_ae_eq_condexp_L1 hm g).symm),
end

lemma condexp_of_ae_strongly_measurable' (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  {f : α → F'} (hf : ae_strongly_measurable' m f μ) (hfi : integrable f μ) :
  μ[f|m] =ᵐ[μ] f :=
begin
  refine ((condexp_congr_ae hf.ae_eq_mk).trans _).trans hf.ae_eq_mk.symm,
  rw condexp_of_strongly_measurable hm hf.strongly_measurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi),
end

lemma integrable_condexp : integrable (μ[f|m]) μ :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, exact integrable_zero _ _ _, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, exact integrable_zero _ _ _, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (integrable_condexp_L1 f).congr (condexp_ae_eq_condexp_L1 hm f).symm,
end

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
lemma set_integral_condexp (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hf : integrable f μ) (hs : measurable_set[m] s) :
  ∫ x in s, μ[f|m] x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexp_L1 hm f).mono (λ x hx _, hx)),
  exact set_integral_condexp_L1 hf hs,
end

lemma integral_condexp (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  (hf : integrable f μ) : ∫ x, μ[f|m] x ∂μ = ∫ x, f x ∂μ :=
begin
  suffices : ∫ x in set.univ, μ[f|m] x ∂μ = ∫ x in set.univ, f x ∂μ,
    by { simp_rw integral_univ at this, exact this, },
  exact set_integral_condexp hm hf (@measurable_set.univ _ m),
end

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
lemma ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  {f g : α → F'} (hf : integrable f μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hg_eq : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
  (hgm : ae_strongly_measurable' m g μ) :
  g =ᵐ[μ] μ[f|m] :=
begin
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite
    (λ s hs hμs, integrable_condexp.integrable_on) (λ s hs hμs, _) hgm
    (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp),
  rw [hg_eq s hs hμs, set_integral_condexp hm hf hs],
end

lemma condexp_bot' [hμ : μ.ae.ne_bot] (f : α → F') :
  μ[f|⊥] = λ _, (μ set.univ).to_real⁻¹ • ∫ x, f x ∂μ :=
begin
  by_cases hμ_finite : is_finite_measure μ,
  swap,
  { have h : ¬ sigma_finite (μ.trim bot_le),
    { rwa sigma_finite_trim_bot_iff, },
    rw not_is_finite_measure_iff at hμ_finite,
    rw [condexp_of_not_sigma_finite bot_le h],
    simp only [hμ_finite, ennreal.top_to_real, inv_zero, zero_smul],
    refl, },
  haveI : is_finite_measure μ := hμ_finite,
  by_cases hf : integrable f μ,
  swap, { rw [integral_undef hf, smul_zero, condexp_undef hf], refl, },
  have h_meas : strongly_measurable[⊥] (μ[f|⊥]) := strongly_measurable_condexp,
  obtain ⟨c, h_eq⟩ := strongly_measurable_bot_iff.mp h_meas,
  rw h_eq,
  have h_integral : ∫ x, μ[f|⊥] x ∂μ = ∫ x, f x ∂μ := integral_condexp bot_le hf,
  simp_rw [h_eq, integral_const] at h_integral,
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul],
  rw [ne.def, ennreal.to_real_eq_zero_iff, auto.not_or_eq, measure.measure_univ_eq_zero,
    ← ae_eq_bot, ← ne.def, ← ne_bot_iff],
  exact ⟨hμ, measure_ne_top μ set.univ⟩,
end

lemma condexp_bot_ae_eq (f : α → F') :
  μ[f|⊥] =ᵐ[μ] λ _, (μ set.univ).to_real⁻¹ • ∫ x, f x ∂μ :=
begin
  by_cases μ.ae.ne_bot,
  { refine eventually_of_forall (λ x, _),
    rw condexp_bot' f,
    exact h, },
  { rw [ne_bot_iff, not_not, ae_eq_bot] at h,
    simp only [h, ae_zero], },
end

lemma condexp_bot [is_probability_measure μ] (f : α → F') :
  μ[f|⊥] = λ _, ∫ x, f x ∂μ :=
by { refine (condexp_bot' f).trans _, rw [measure_univ, ennreal.one_to_real, inv_one, one_smul], }

lemma condexp_add (hf : integrable f μ) (hg : integrable g μ) :
  μ[f + g | m] =ᵐ[μ] μ[f|m] + μ[g|m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, simp, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, simp, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  refine (condexp_ae_eq_condexp_L1 hm _).trans _,
  rw condexp_L1_add hf hg,
  exact (coe_fn_add _ _).trans
    ((condexp_ae_eq_condexp_L1 hm _).symm.add (condexp_ae_eq_condexp_L1 hm _).symm),
end

lemma condexp_finset_sum {ι : Type*} {s : finset ι} {f : ι → α → F'}
  (hf : ∀ i ∈ s, integrable (f i) μ) :
  μ[∑ i in s, f i | m] =ᵐ[μ] ∑ i in s, μ[f i | m] :=
begin
  induction s using finset.induction_on with i s his heq hf,
  { rw [finset.sum_empty, finset.sum_empty, condexp_zero] },
  { rw [finset.sum_insert his, finset.sum_insert his],
    exact (condexp_add (hf i $ finset.mem_insert_self i s) $ integrable_finset_sum' _
      (λ j hmem, hf j $ finset.mem_insert_of_mem hmem)).trans
      ((eventually_eq.refl _ _).add (heq $ λ j hmem, hf j $ finset.mem_insert_of_mem hmem)) }
end

lemma condexp_smul (c : 𝕜) (f : α → F') : μ[c • f | m] =ᵐ[μ] c • μ[f|m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, simp, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, simp, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  refine (condexp_ae_eq_condexp_L1 hm _).trans _,
  rw condexp_L1_smul c f,
  refine (@condexp_ae_eq_condexp_L1 _ _ _ _ _ m _ _ hm _ f).mp _,
  refine (coe_fn_smul c (condexp_L1 hm μ f)).mono (λ x hx1 hx2, _),
  rw [hx1, pi.smul_apply, pi.smul_apply, hx2],
end

lemma condexp_neg (f : α → F') : μ[-f|m] =ᵐ[μ] - μ[f|m] :=
by letI : module ℝ (α → F') := @pi.module α (λ _, F') ℝ _ _ (λ _, infer_instance);
calc μ[-f|m] = μ[(-1 : ℝ) • f|m] : by rw neg_one_smul ℝ f
... =ᵐ[μ] (-1 : ℝ) • μ[f|m] : condexp_smul (-1) f
... = -μ[f|m] : neg_one_smul ℝ (μ[f|m])

lemma condexp_sub (hf : integrable f μ) (hg : integrable g μ) :
  μ[f - g | m] =ᵐ[μ] μ[f|m] - μ[g|m] :=
begin
  simp_rw sub_eq_add_neg,
  exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g)),
end

lemma condexp_condexp_of_le {m₁ m₂ m0 : measurable_space α} {μ : measure α} (hm₁₂ : m₁ ≤ m₂)
  (hm₂ : m₂ ≤ m0) [sigma_finite (μ.trim hm₂)] :
  μ[ μ[f|m₂] | m₁] =ᵐ[μ] μ[f | m₁] :=
begin
  by_cases hμm₁ : sigma_finite (μ.trim (hm₁₂.trans hm₂)),
  swap, { simp_rw condexp_of_not_sigma_finite (hm₁₂.trans hm₂) hμm₁, },
  haveI : sigma_finite (μ.trim (hm₁₂.trans hm₂)) := hμm₁,
  by_cases hf : integrable f μ,
  swap, { simp_rw [condexp_undef hf, condexp_zero], },
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm₁₂.trans hm₂)
    (λ s hs hμs, integrable_condexp.integrable_on) (λ s hs hμs, integrable_condexp.integrable_on)
    _ (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp),
  intros s hs hμs,
  rw set_integral_condexp (hm₁₂.trans hm₂) integrable_condexp hs,
  swap, { apply_instance, },
  rw [set_integral_condexp (hm₁₂.trans hm₂) hf hs, set_integral_condexp hm₂ hf (hm₁₂ s hs)],
end

lemma condexp_mono {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f g : α → E} (hf : integrable f μ) (hg : integrable g μ) (hfg : f ≤ᵐ[μ] g) :
  μ[f | m] ≤ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (condexp_ae_eq_condexp_L1 hm _).trans_le
    ((condexp_L1_mono hf hg hfg).trans_eq (condexp_ae_eq_condexp_L1 hm _).symm),
end

lemma condexp_nonneg {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f : α → E} (hf : 0 ≤ᵐ[μ] f) :
  0 ≤ᵐ[μ] μ[f | m] :=
begin
  by_cases hfint : integrable f μ,
  { rw (condexp_zero.symm : (0 : α → E) = μ[0 | m]),
    exact condexp_mono (integrable_zero _ _ _) hfint hf },
  { rw condexp_undef hfint, }
end

lemma condexp_nonpos {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f : α → E} (hf : f ≤ᵐ[μ] 0) :
  μ[f | m] ≤ᵐ[μ] 0 :=
begin
  by_cases hfint : integrable f μ,
  { rw (condexp_zero.symm : (0 : α → E) = μ[0 | m]),
    exact condexp_mono hfint (integrable_zero _ _ _) hf },
  { rw condexp_undef hfint, }
end

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condexp_L1`. -/
lemma tendsto_condexp_L1_of_dominated_convergence (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  {fs : ℕ → α → F'} {f : α → F'} (bound_fs : α → ℝ)
  (hfs_meas : ∀ n, ae_strongly_measurable (fs n) μ) (h_int_bound_fs : integrable bound_fs μ)
  (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
  (hfs : ∀ᵐ x ∂μ, tendsto (λ n, fs n x) at_top (𝓝 (f x))) :
  tendsto (λ n, condexp_L1 hm μ (fs n)) at_top (𝓝 (condexp_L1 hm μ f)) :=
tendsto_set_to_fun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs

/-- If two sequences of functions have a.e. equal conditional expectations at each step, converge
and verify dominated convergence hypotheses, then the conditional expectations of their limits are
a.e. equal. -/
lemma tendsto_condexp_unique (fs gs : ℕ → α → F') (f g : α → F')
  (hfs_int : ∀ n, integrable (fs n) μ) (hgs_int : ∀ n, integrable (gs n) μ)
  (hfs : ∀ᵐ x ∂μ, tendsto (λ n, fs n x) at_top (𝓝 (f x)))
  (hgs : ∀ᵐ x ∂μ, tendsto (λ n, gs n x) at_top (𝓝 (g x)))
  (bound_fs : α → ℝ) (h_int_bound_fs : integrable bound_fs μ)
  (bound_gs : α → ℝ) (h_int_bound_gs : integrable bound_gs μ)
  (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
  (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x)
  (hfg : ∀ n, μ[fs n | m] =ᵐ[μ] μ[gs n | m]) :
  μ[f | m] =ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0, swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm), swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  refine (condexp_ae_eq_condexp_L1 hm f).trans ((condexp_ae_eq_condexp_L1 hm g).trans _).symm,
  rw ← Lp.ext_iff,
  have hn_eq : ∀ n, condexp_L1 hm μ (gs n) = condexp_L1 hm μ (fs n),
  { intros n,
    ext1,
    refine (condexp_ae_eq_condexp_L1 hm (gs n)).symm.trans ((hfg n).symm.trans _),
    exact (condexp_ae_eq_condexp_L1 hm (fs n)), },
  have hcond_fs : tendsto (λ n, condexp_L1 hm μ (fs n)) at_top (𝓝 (condexp_L1 hm μ f)),
    from tendsto_condexp_L1_of_dominated_convergence hm _ (λ n, (hfs_int n).1) h_int_bound_fs
       hfs_bound hfs,
  have hcond_gs : tendsto (λ n, condexp_L1 hm μ (gs n)) at_top (𝓝 (condexp_L1 hm μ g)),
    from tendsto_condexp_L1_of_dominated_convergence hm _ (λ n, (hgs_int n).1) h_int_bound_gs
       hgs_bound hgs,
  exact tendsto_nhds_unique_of_eventually_eq hcond_gs hcond_fs (eventually_of_forall hn_eq),
end

end measure_theory

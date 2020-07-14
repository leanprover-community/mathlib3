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
  Then `f` is called `integrable` if `(∫⁻ a, nnnorm (f a)) < ⊤` holds.

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

## Tags

integrable, function space, l1

-/

noncomputable theory
open_locale classical topological_space


namespace measure_theory
open set filter topological_space ennreal emetric
open_locale big_operators

universes u v w
variables {α : Type u} [measurable_space α] {μ : measure α}
variables {β : Type v} [normed_group β] {γ : Type w} [normed_group γ]

/-- A function is `integrable` if the integral of its pointwise norm is less than infinity. -/
def integrable (μ : measure α) (f : α → β) : Prop := ∫⁻ a, nnnorm (f a) ∂μ < ⊤

lemma integrable_iff_norm (f : α → β) : integrable μ f ↔ ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ < ⊤ :=
by simp only [integrable, of_real_norm_eq_coe_nnnorm]

lemma integrable_iff_edist (f : α → β) : integrable μ  f ↔ ∫⁻ a, edist (f a) 0 ∂μ < ⊤ :=
by simp only [integrable_iff_norm, edist_dist, dist_zero_right]

lemma integrable_iff_of_real {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
  integrable μ f ↔ ∫⁻ a, ennreal.of_real (f a) ∂μ < ⊤ :=
have lintegral_eq : ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ = ∫⁻ a, ennreal.of_real (f a) ∂μ :=
begin
  refine lintegral_congr_ae (h.mono $ λ a h, _),
  rwa [real.norm_eq_abs, abs_of_nonneg]
end,
by rw [integrable_iff_norm, lintegral_eq]

lemma integrable.congr {f g : α → β} (hf : integrable μ f) (h : f =ᵐ[μ] g) : integrable μ g :=
begin
  simp only [integrable],
  convert hf using 1,
  exact lintegral_rw₁ (h.symm.fun_comp _) _
end

lemma integrable_congr {f g : α → β} (h : f =ᵐ[μ] g) : integrable μ f ↔ integrable μ g :=
⟨λ hf, hf.congr h, λ hg, hg.congr h.symm⟩

lemma integrable.mono {f : α → β} {g : α → γ} (hg : integrable μ g) (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) :
  integrable μ f :=
begin
  simp only [integrable_iff_norm] at *,
  calc ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ ≤ ∫⁻ (a : α), (ennreal.of_real ∥g a∥) ∂μ :
    lintegral_mono_ae (h.mono $ assume a h, of_real_le_of_real h)
    ... < ⊤ : hg
end

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

lemma lintegral_edist_lt_top [second_countable_topology β] [measurable_space β]
  [opens_measurable_space β] {f g : α → β}
  (hfm : measurable f) (hfi : integrable μ f) (hgm : measurable g) (hgi : integrable μ g) :
  ∫⁻ a, edist (f a) (g a) ∂μ < ⊤ :=
lt_of_le_of_lt
  (lintegral_edist_triangle hfm hgm (measurable_const : measurable (λa, (0 : β))))
  (ennreal.add_lt_top.2 $ by { split; rw ← integrable_iff_edist; assumption })

lemma lintegral_nnnorm_zero : ∫⁻ a : α, nnnorm (0 : β) ∂μ = 0 := by simp

variables (α β μ)
@[simp] lemma integrable_zero : integrable μ (λa:α, (0:β)) :=
by simp [integrable]
variables {α β μ}

lemma lintegral_nnnorm_add [measurable_space β] [opens_measurable_space β]
  [measurable_space γ] [opens_measurable_space γ]
  {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g) :
  ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ = ∫⁻ a, nnnorm (f a) ∂μ + ∫⁻ a, nnnorm (g a) ∂μ :=
lintegral_add hf.ennnorm hg.ennnorm

lemma integrable.add [measurable_space β] [opens_measurable_space β]
  {f g : α → β} (hfm : measurable f) (hfi : integrable μ f)
  (hgm : measurable g) (hgi : integrable μ g) :
  integrable μ (f + g) :=
calc
  ∫⁻ a, nnnorm (f a + g a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ :
    lintegral_mono
      (assume a, by { simp only [← coe_add, coe_le_coe], exact nnnorm_add_le _ _ })
  ... = _ :
    lintegral_nnnorm_add hfm hgm
  ... < ⊤ : add_lt_top.2 ⟨hfi, hgi⟩

lemma integrable_finset_sum {ι} [measurable_space β] [borel_space β]
  [second_countable_topology β] (s : finset ι) {f : ι → α → β}
  (hfm : ∀ i, measurable (f i)) (hfi : ∀ i, integrable μ (f i)) :
  integrable μ (λ a, ∑ i in s, f i a) :=
begin
  refine finset.induction_on s _ _,
  { simp only [finset.sum_empty, integrable_zero] },
  { assume i s his ih,
    simp only [his, finset.sum_insert, not_false_iff],
    refine (hfi _).add (hfm _) (s.measurable_sum hfm) ih }
end

lemma lintegral_nnnorm_neg {f : α → β} :
  ∫⁻ a, nnnorm ((-f) a) ∂μ = ∫⁻ a, nnnorm (f a) ∂μ :=
by simp only [pi.neg_apply, nnnorm_neg]

lemma integrable.neg {f : α → β} (hfi : integrable μ f) : integrable μ (-f) :=
calc _ = _ : lintegral_nnnorm_neg
   ... < ⊤ : hfi

@[simp] lemma integrable_neg_iff {f : α → β} : integrable μ (-f) ↔ integrable μ f :=
⟨λ h, neg_neg f ▸ h.neg, integrable.neg⟩

lemma integrable.sub [measurable_space β] [opens_measurable_space β]
  {f g : α → β} (hfm : measurable f) (hfi : integrable μ f) (hgm : measurable g)
  (hgi : integrable μ g) : integrable μ (f - g) :=
calc
  ∫⁻ a, nnnorm (f a - g a) ∂μ ≤ ∫⁻ a, nnnorm (f a) + nnnorm (-g a) ∂μ :
    lintegral_mono (assume a, by exact_mod_cast nnnorm_add_le _ _ )
  ... = _ :
    by { simp only [nnnorm_neg], exact lintegral_nnnorm_add hfm hgm }
  ... < ⊤ : add_lt_top.2 ⟨hfi, hgi⟩

lemma integrable.norm {f : α → β} (hfi : integrable μ f) : integrable μ (λa, ∥f a∥) :=
have eq : (λa, (nnnorm ∥f a∥ : ennreal)) = λa, (nnnorm (f a) : ennreal),
  by { funext, rw nnnorm_norm },
by { rwa [integrable, eq] }

lemma integrable_norm_iff (f : α → β) : integrable μ (λa, ∥f a∥) ↔ integrable μ f :=
have eq : (λa, (nnnorm ∥f a∥ : ennreal)) = λa, (nnnorm (f a) : ennreal),
  by { funext, rw nnnorm_norm },
by { rw [integrable, integrable, eq] }

lemma integrable_of_integrable_bound {f : α → β} {bound : α → ℝ} (h : integrable μ bound)
  (h_bound : ∀ᵐ a ∂μ, ∥f a∥ ≤ bound a) : integrable μ f :=
have h₁ : ∀ᵐ a ∂μ, (nnnorm (f a) : ennreal) ≤ ennreal.of_real (bound a),
begin
  filter_upwards [h_bound],
  simp only [mem_set_of_eq],
  assume a h,
  calc (nnnorm (f a) : ennreal) = ennreal.of_real (∥f a∥) : by rw of_real_norm_eq_coe_nnnorm
    ... ≤ ennreal.of_real (bound a) : ennreal.of_real_le_of_real h
end,
calc ∫⁻ a, nnnorm (f a) ∂μ ≤ ∫⁻ a, ennreal.of_real (bound a) ∂μ :
    lintegral_mono_ae h₁
  ... ≤ ∫⁻ a, (ennreal.of_real ∥bound a∥) ∂μ : lintegral_mono $
    assume a, ennreal.of_real_le_of_real $ le_max_left (bound a) (-bound a)
  ... < ⊤ : by { rwa [integrable_iff_norm] at h }

section dominated_convergence

variables {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

lemma all_ae_of_real_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a) :
  ∀ n, ∀ᵐ a ∂μ, ennreal.of_real ∥F n a∥ ≤ ennreal.of_real (bound a) :=
λn, by filter_upwards [h n] λ a h, ennreal.of_real_le_of_real h

lemma all_ae_tendsto_of_real_norm (h : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top $ 𝓝 $ f a) :
  ∀ᵐ a ∂μ, tendsto (λn, ennreal.of_real ∥F n a∥) at_top $ 𝓝 $ ennreal.of_real ∥f a∥ :=
by filter_upwards [h]
  λ a h, tendsto_of_real $ tendsto.comp (continuous.tendsto continuous_norm _) h

lemma all_ae_of_real_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  ∀ᵐ a ∂μ, ennreal.of_real ∥f a∥ ≤ ennreal.of_real (bound a) :=
begin
  have F_le_bound := all_ae_of_real_F_le_bound h_bound,
  rw ← ae_all_iff at F_le_bound,
  apply F_le_bound.mp ((all_ae_tendsto_of_real_norm h_lim).mono _),
  assume a tendsto_norm F_le_bound,
  exact le_of_tendsto' at_top_ne_bot tendsto_norm (F_le_bound)
end

lemma integrable_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (bound_integrable : integrable μ bound)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  integrable μ f :=
/- `∥F n a∥ ≤ bound a` and `∥F n a∥ --> ∥f a∥` implies `∥f a∥ ≤ bound a`,
  and so `∫ ∥f∥ ≤ ∫ bound < ⊤` since `bound` is integrable -/
begin
  rw integrable_iff_norm,
  calc ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ ≤ ∫⁻ a, ennreal.of_real (bound a) ∂μ :
    lintegral_mono_ae $ all_ae_of_real_f_le_bound h_bound h_lim
    ... < ⊤ :
    begin
      rw ← integrable_iff_of_real,
      { exact bound_integrable },
      filter_upwards [h_bound 0] λ a h, le_trans (norm_nonneg _) h,
    end
end

lemma tendsto_lintegral_norm_of_dominated_convergence [measurable_space β]
  [borel_space β] [second_countable_topology β]
  {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (F_measurable : ∀ n, measurable (F n))
  (f_measurable : measurable f)
  (bound_integrable : integrable μ bound)
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
  suffices h : ∀ᵐ a ∂μ, tendsto (λ n, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 $ ennreal.of_real 0),
  { rwa ennreal.of_real_zero at h },
  filter_upwards [h_lim],
  assume a h,
  refine tendsto.comp (continuous.tendsto continuous_of_real _) _,
  rw ← tendsto_iff_norm_tendsto_zero,
  exact h
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
  -- Show `2 * bound` is integrable
  { rw integrable_iff_of_real at bound_integrable,
    { calc ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ennreal.of_real (bound a) ∂μ :
        by { rw lintegral_const_mul', exact coe_ne_top }
        ... < ⊤ : mul_lt_top (coe_lt_top) bound_integrable },
    filter_upwards [h_bound 0] λ a h, le_trans (norm_nonneg _) h },
  -- Show `∥f a - F n a∥ --> 0`
  { exact h }
end

end dominated_convergence

section pos_part
/-! Lemmas used for defining the positive part of a `L¹` function -/

lemma integrable.max_zero {f : α → ℝ} (hf : integrable μ f) : integrable μ (λa, max (f a) 0) :=
begin
  simp only [integrable_iff_norm] at *,
  calc ∫⁻ a, (ennreal.of_real ∥max (f a) 0∥) ∂μ ≤ ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ :
    lintegral_mono
    begin
      assume a,
      apply of_real_le_of_real,
      simp only [real.norm_eq_abs],
      calc abs (max (f a) 0) = max (f a) 0 : by { rw abs_of_nonneg, apply le_max_right }
        ... ≤ abs (f a) : max_le (le_abs_self _) (abs_nonneg _)
    end
    ... < ⊤ : hf
end

lemma integrable.min_zero {f : α → ℝ} (hf : integrable μ f) : integrable μ (λa, min (f a) 0) :=
begin
  have : (λa, min (f a) 0) = (λa, - max (-f a) 0),
  { funext, rw [min_eq_neg_max_neg_neg, neg_zero] },
  rw this,
  exact (integrable.max_zero hf.neg).neg,
end

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable.smul (c : 𝕜) {f : α → β} : integrable μ f → integrable μ (c • f) :=
begin
  simp only [integrable], assume hfi,
  calc
    ∫⁻ (a : α), nnnorm (c • f a) ∂μ = ∫⁻ (a : α), (nnnorm c) * nnnorm (f a) ∂μ :
      by simp only [nnnorm_smul, ennreal.coe_mul]
    ... < ⊤ :
    begin
      rw lintegral_const_mul',
      exacts [mul_lt_top coe_lt_top hfi, coe_ne_top]
    end
end

lemma integrable_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  integrable μ (c • f) ↔ integrable μ f :=
begin
  split,
  { assume h,
    simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.smul c⁻¹ },
  exact integrable.smul _
end

end normed_space

variables [second_countable_topology β]

namespace ae_eq_fun

variable [measurable_space β]

section

variable [opens_measurable_space β]

/-- An almost everywhere equal function is `integrable` if it has a finite distance to the origin.
  Should mean the same thing as the predicate `integrable` over functions. -/
def integrable (f : α →ₘ[μ] β) : Prop := f ∈ ball (0 : α →ₘ[μ] β) ⊤

lemma integrable_mk {f : α → β} (hf : measurable f) :
  (integrable (mk f hf : α →ₘ[μ] β)) ↔ measure_theory.integrable μ f :=
by simp [integrable, zero_def, edist_mk_mk', measure_theory.integrable, nndist_eq_nnnorm]

lemma integrable_coe_fn (f : α →ₘ[μ] β) : (measure_theory.integrable μ f) ↔ integrable f :=
by rw [← integrable_mk, mk_coe_fn]

local attribute [simp] integrable_mk

lemma integrable_zero : integrable (0 : α →ₘ[μ] β) := mem_ball_self coe_lt_top

end

section

variable [borel_space β]

lemma integrable.add {f g : α →ₘ[μ] β} : integrable f → integrable g → integrable (f + g) :=
begin
  refine induction_on₂ f g (λ f hf g hg, _),
  simp only [integrable_mk, mk_add_mk],
  exact λ hfi hgi, hfi.add hf hg hgi
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

variables (α β)
/-- The space of equivalence classes of integrable (and measurable) functions, where two integrable
    functions are equivalent if they agree almost everywhere, i.e., they differ on a set of measure
    `0`. -/
def l1 [measurable_space β] [opens_measurable_space β] (μ : measure α) : Type (max u v) := {f : α →ₘ[μ] β // f.integrable}

notation α ` →₁[`:25 μ `] ` β := l1 α β μ

variables {α β}

namespace l1
open ae_eq_fun
local attribute [instance] ae_eq_fun.is_add_subgroup

variables [measurable_space β]

section

variable [opens_measurable_space β]

instance : has_coe (α →₁[μ] β) (α →ₘ[μ] β) := coe_subtype

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
@[simp, norm_cast] lemma coe_add (f g : α →₁[μ] β) : ((f + g : α →₁[μ] β) : α →ₘ[μ] β) = f + g := rfl
@[simp, norm_cast] lemma coe_neg (f : α →₁[μ] β) : ((-f : α →₁[μ] β) : α →ₘ[μ] β) = -f := rfl
@[simp, norm_cast] lemma coe_sub (f g : α →₁[μ] β) : ((f - g : α →₁[μ] β) : α →ₘ[μ] β) = f - g := rfl

@[simp] lemma edist_eq (f g : α →₁[μ] β) : edist f g = edist (f : α →ₘ[μ] β) (g : α →ₘ[μ] β) := rfl

lemma dist_eq (f g : α →₁[μ] β) : dist f g = ennreal.to_real (edist (f : α →ₘ[μ] β) (g : α →ₘ[μ] β)) := rfl

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
def of_fun (f : α → β) (hfm : measurable f) (hfi : integrable μ f) : (α →₁[μ] β) :=
⟨mk f hfm, by { rw integrable_mk, exact hfi }⟩

@[simp] lemma of_fun_eq_mk (f : α → β) (hfm hfi) :
  ((of_fun f hfm hfi : α →₁[μ] β) : α →ₘ[μ] β) = mk f hfm :=
rfl

lemma of_fun_eq_of_fun (f g : α → β) (hfm hfi hgm hgi) :
  (of_fun f hfm hfi : α →₁[μ] β) = of_fun g hgm hgi ↔ f =ᵐ[μ] g :=
by { rw ← l1.eq_iff, simp only [of_fun_eq_mk, mk_eq_mk] }

lemma of_fun_zero :
  (of_fun (λ _, 0) measurable_zero (integrable_zero α μ β) : α →₁[μ] β) = 0 := rfl

lemma of_fun_add (f g : α → β) (hfm hfi hgm hgi) :
  (of_fun (f + g) (measurable.add hfm hgm) (integrable.add hfm hfi hgm hgi) : α →₁[μ] β)
    = of_fun f hfm hfi + of_fun g hgm hgi :=
rfl

lemma of_fun_neg (f : α → β) (hfm hfi) :
  (of_fun (- f) (measurable.neg hfm) (integrable.neg hfi) : α →₁[μ] β) = - of_fun f hfm hfi := rfl

lemma of_fun_sub (f g : α → β) (hfm hfi hgm hgi) :
  (of_fun (f - g) (measurable.sub hfm hgm) (integrable.sub hfm hfi hgm hgi) : α →₁[μ] β)
    = of_fun f hfm hfi - of_fun g hgm hgi :=
rfl

lemma norm_of_fun (f : α → β) (hfm hfi) :
  ∥(of_fun f hfm hfi : α →₁[μ] β)∥ = ennreal.to_real (∫⁻ a, edist (f a) 0 ∂μ) :=
rfl

lemma norm_of_fun_eq_lintegral_norm (f : α → β) (hfm hfi) :
  ∥(of_fun f hfm hfi : α →₁[μ] β)∥ = ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :=
by { rw [norm_of_fun, lintegral_norm_eq_lintegral_edist] }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma of_fun_smul (f : α → β) (hfm : measurable f) (hfi : integrable μ f) (k : 𝕜) :
  of_fun (λa, k • f a) (hfm.const_smul _) (hfi.smul _) = k • of_fun f hfm hfi := rfl

end of_fun

section to_fun

/-- Find a representative of an `L¹` function [f] -/
@[reducible]
protected def to_fun (f : α →₁[μ] β) : α → β := (f : α →ₘ[μ] β)

protected lemma measurable (f : α →₁[μ] β) : measurable f.to_fun := f.1.measurable

protected lemma integrable (f : α →₁[μ] β) : integrable μ f.to_fun :=
by { rw [l1.to_fun, integrable_coe_fn], exact f.2 }

lemma of_fun_to_fun (f : α →₁[μ] β) : of_fun (f.to_fun) f.measurable f.integrable = f :=
begin
  rcases f with ⟨f, hfi⟩,
  rw [of_fun, subtype.mk_eq_mk],
  exact f.mk_coe_fn
end

lemma mk_to_fun (f : α →₁[μ] β) : (mk (f.to_fun) f.measurable : α →ₘ[μ] β)= f :=
by { rw ← of_fun_eq_mk, rw l1.eq_iff, exact of_fun_to_fun f }

lemma to_fun_of_fun (f : α → β) (hfm hfi) :
  (of_fun f hfm hfi : α →₁[μ] β).to_fun =ᵐ[μ] f :=
coe_fn_mk f hfm

variables (α β)
lemma zero_to_fun : (0 : α →₁[μ] β).to_fun =ᵐ[μ] 0 := ae_eq_fun.coe_fn_zero
variables {α β}

lemma add_to_fun (f g : α →₁[μ] β) : (f + g).to_fun =ᵐ[μ] f.to_fun + g.to_fun :=
ae_eq_fun.coe_fn_add _ _

lemma neg_to_fun (f : α →₁[μ] β) : (-f).to_fun =ᵐ[μ] -f.to_fun := ae_eq_fun.coe_fn_neg _

lemma sub_to_fun (f g : α →₁[μ] β) : (f - g).to_fun =ᵐ[μ] f.to_fun - g.to_fun :=
ae_eq_fun.coe_fn_sub _ _

lemma dist_to_fun (f g : α →₁[μ] β) :
  dist f g = ennreal.to_real (∫⁻ x, edist (f.to_fun x) (g.to_fun x) ∂μ) :=
by { simp only [dist_eq, edist_eq_coe] }

lemma norm_eq_nnnorm_to_fun (f : α →₁[μ] β) : ∥f∥ = ennreal.to_real (∫⁻ a, nnnorm (f.to_fun a) ∂μ) :=
by { rw [lintegral_nnnorm_eq_lintegral_edist, ← edist_zero_eq_coe], refl }

lemma norm_eq_norm_to_fun (f : α →₁[μ] β) :
  ∥f∥ = ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f.to_fun a∥) ∂μ) :=
by { rw norm_eq_nnnorm_to_fun, congr, funext, rw of_real_norm_eq_coe_nnnorm }

lemma lintegral_edist_to_fun_lt_top (f g : α →₁[μ] β) : (∫⁻ a, edist (f.to_fun a) (g.to_fun a) ∂μ) < ⊤ :=
begin
  apply lintegral_edist_lt_top,
  exact f.measurable, exact f.integrable, exact g.measurable, exact g.integrable
end

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma smul_to_fun (c : 𝕜) (f : α →₁[μ] β) : (c • f).to_fun =ᵐ[μ] c • f.to_fun :=
ae_eq_fun.coe_fn_smul _ _

end to_fun

section pos_part

/-- Positive part of a function in `L¹` space. -/
def pos_part (f : α →₁[μ] ℝ) : α →₁[μ] ℝ :=
⟨ae_eq_fun.pos_part f,
  begin
    rw [← ae_eq_fun.integrable_coe_fn, integrable_congr (coe_fn_pos_part _)],
    exact integrable.max_zero f.integrable
  end ⟩

/-- Negative part of a function in `L¹` space. -/
def neg_part (f : α →₁[μ] ℝ) : α →₁[μ] ℝ := pos_part (-f)

@[norm_cast] lemma coe_pos_part (f : α →₁[μ] ℝ) : (f.pos_part : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part := rfl

lemma pos_part_to_fun (f : α →₁[μ] ℝ) : (pos_part f).to_fun =ᵐ[μ] λ a, max (f.to_fun a) 0 :=
ae_eq_fun.coe_fn_pos_part _

lemma neg_part_to_fun_eq_max (f : α →₁[μ] ℝ) : ∀ᵐ a ∂μ, (neg_part f).to_fun a = max (- f.to_fun a) 0 :=
begin
  rw neg_part,
  filter_upwards [pos_part_to_fun (-f), neg_to_fun f],
  simp only [mem_set_of_eq],
  assume a h₁ h₂,
  rw [h₁, h₂, pi.neg_apply]
end

lemma neg_part_to_fun_eq_min (f : α →₁[μ] ℝ) : ∀ᵐ a ∂μ, (neg_part f).to_fun a = - min (f.to_fun a) 0 :=
begin
  filter_upwards [neg_part_to_fun_eq_max f],
  simp only [mem_set_of_eq],
  assume a h,
  rw [h, min_eq_neg_max_neg_neg, _root_.neg_neg, neg_zero],
end

lemma norm_le_norm_of_ae_le {f g : α →₁[μ] β} (h : ∀ᵐ a ∂μ, ∥f.to_fun a∥ ≤ ∥g.to_fun a∥) : ∥f∥ ≤ ∥g∥ :=
begin
  simp only [l1.norm_eq_norm_to_fun],
  rw to_real_le_to_real,
  { apply lintegral_mono_ae,
    exact h.mono (λ a h, of_real_le_of_real h) },
  { rw [← lt_top_iff_ne_top, ← integrable_iff_norm], exact f.integrable },
  { rw [← lt_top_iff_ne_top, ← integrable_iff_norm], exact g.integrable }
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

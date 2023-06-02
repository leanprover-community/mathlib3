/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.cond_distrib

/-!
# Kernel associated with a conditional expectation

We define `condexp_kernel μ m`, a kernel from `Ω` to `Ω` such that for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)`.

This kernel is defined if `Ω` is a standard Borel space. In general, `μ⟦s | m⟧` maps a measurable
set `s` to a function `Ω → ℝ≥0∞`, and for all `s` that map is unique up to a `μ`-null set. For all
`a`, the map from sets to `ℝ≥0∞` that we obtain that way verifies some of the properties of a
measure, but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of
the conditional expectation that combine into a true measure. The standard Borel space assumption
on `Ω` allows us to do so.

## Main definitions

* `condexp_kernel μ m`: kernel such that `μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)`.

## Main statements

* `condexp_ae_eq_integral_condexp_kernel`: `μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)`.

-/

open measure_theory set filter topological_space

open_locale ennreal measure_theory probability_theory

namespace probability_theory

section aux_lemmas

variables {Ω F : Type*} {m mΩ : measurable_space Ω} {μ : measure Ω} {f : Ω → F}

-- todo after the port: move to measure_theory/measurable_space, after measurable.mono
lemma measurable_id'' (hm : m ≤ mΩ) :
  @measurable Ω Ω mΩ m id :=
measurable_id.mono le_rfl hm

-- todo after the port: move to measure_theory/measurable_space, after measurable.mono
lemma ae_measurable_id'' (μ : measure Ω) (hm : m ≤ mΩ) :
  @ae_measurable Ω Ω m mΩ id μ :=
@measurable.ae_measurable Ω Ω mΩ m id μ (measurable_id'' hm)

lemma _root_.measure_theory.ae_strongly_measurable.comp_snd_map_prod_id [topological_space F]
  (hm : m ≤ mΩ) (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x : Ω × Ω, f x.2)
    (@measure.map Ω (Ω × Ω) (m.prod mΩ) mΩ (λ ω, (id ω, id ω)) μ) :=
begin
  rw ← ae_strongly_measurable_comp_snd_map_prod_mk_iff (measurable_id'' hm) at hf,
  simp_rw [id.def] at hf ⊢,
  exact hf,
end

lemma _root_.measure_theory.integrable.comp_snd_map_prod_id [normed_add_comm_group F]
  (hm : m ≤ mΩ) (hf : integrable f μ) :
  integrable (λ x : Ω × Ω, f x.2)
    (@measure.map Ω (Ω × Ω) (m.prod mΩ) mΩ (λ ω, (id ω, id ω)) μ) :=
begin
  rw ← integrable_comp_snd_map_prod_mk_iff (measurable_id'' hm) at hf,
  simp_rw [id.def] at hf ⊢,
  exact hf,
end

end aux_lemmas

variables {Ω F : Type*} [topological_space Ω] {m : measurable_space Ω} [mΩ : measurable_space Ω]
  [polish_space Ω] [borel_space Ω] [nonempty Ω]
  {μ : measure Ω} [is_finite_measure μ]
  [normed_add_comm_group F] {f : Ω → F}

/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m`. -/
@[irreducible] noncomputable
def condexp_kernel (μ : measure Ω) [is_finite_measure μ] (m : measurable_space Ω) :
  @kernel Ω Ω m mΩ :=
@cond_distrib Ω Ω Ω _ mΩ _ _ _ mΩ m id id μ _

section measurability

lemma measurable_condexp_kernel {s : set Ω} (hs : measurable_set s) :
  measurable[m] (λ ω, condexp_kernel μ m ω s) :=
by { rw condexp_kernel, convert measurable_cond_distrib hs, rw measurable_space.comap_id, }

lemma _root_.measure_theory.ae_strongly_measurable.integral_condexp_kernel
  [normed_space ℝ F] [complete_space F]
  (hm : m ≤ mΩ) (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)) μ :=
begin
  rw condexp_kernel,
  exact ae_strongly_measurable.integral_cond_distrib
    (ae_measurable_id'' μ hm) ae_measurable_id (hf.comp_snd_map_prod_id hm),
end

lemma ae_strongly_measurable'_integral_condexp_kernel [normed_space ℝ F] [complete_space F]
  (hm : m ≤ mΩ) (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable' m (λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)) μ :=
begin
  rw condexp_kernel,
  have h := ae_strongly_measurable'_integral_cond_distrib
    (ae_measurable_id'' μ hm) ae_measurable_id (hf.comp_snd_map_prod_id hm),
  rwa measurable_space.comap_id at h,
end

end measurability

section integrability

lemma _root_.measure_theory.integrable.condexp_kernel_ae
  (hm : m ≤ mΩ) (hf_int : integrable f μ) :
  ∀ᵐ ω ∂μ, integrable f (condexp_kernel μ m ω) :=
begin
  rw condexp_kernel,
  exact integrable.cond_distrib_ae (ae_measurable_id'' μ hm)
    ae_measurable_id (hf_int.comp_snd_map_prod_id hm),
end

lemma _root_.measure_theory.integrable.integral_norm_condexp_kernel
  (hm : m ≤ mΩ) (hf_int : integrable f μ) :
  integrable (λ ω, ∫ y, ‖f y‖ ∂(condexp_kernel μ m ω)) μ :=
begin
  rw condexp_kernel,
  exact integrable.integral_norm_cond_distrib (ae_measurable_id'' μ hm)
    ae_measurable_id (hf_int.comp_snd_map_prod_id hm),
end

lemma _root_.measure_theory.integrable.norm_integral_condexp_kernel
  [normed_space ℝ F] [complete_space F]
  (hm : m ≤ mΩ) (hf_int : integrable f μ) :
  integrable (λ ω, ‖∫ y, f y ∂(condexp_kernel μ m ω)‖) μ :=
begin
  rw condexp_kernel,
  exact integrable.norm_integral_cond_distrib (ae_measurable_id'' μ hm)
    ae_measurable_id (hf_int.comp_snd_map_prod_id hm),
end

lemma _root_.measure_theory.integrable.integral_condexp_kernel [normed_space ℝ F] [complete_space F]
  (hm : m ≤ mΩ) (hf_int : integrable f μ) :
  integrable (λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)) μ :=
begin
  rw condexp_kernel,
  exact integrable.integral_cond_distrib (ae_measurable_id'' μ hm)
    ae_measurable_id (hf_int.comp_snd_map_prod_id hm),
end

lemma integrable_to_real_condexp_kernel (hm : m ≤ mΩ) {s : set Ω} (hs : measurable_set s) :
  integrable (λ ω, (condexp_kernel μ m ω s).to_real) μ :=
begin
  rw condexp_kernel,
  exact integrable_to_real_cond_distrib (ae_measurable_id'' μ hm) hs,
end

end integrability

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condexp_kernel μ m ω)`. -/
lemma condexp_ae_eq_integral_condexp_kernel [normed_space ℝ F] [complete_space F]
  (hm : m ≤ mΩ) (hf_int : integrable f μ) :
  μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω) :=
begin
  have hX : @measurable Ω Ω mΩ m id := measurable_id.mono le_rfl hm,
  rw condexp_kernel,
  refine eventually_eq.trans _ (condexp_ae_eq_integral_cond_distrib_id hX hf_int),
  simp only [measurable_space.comap_id, id.def],
end

end probability_theory

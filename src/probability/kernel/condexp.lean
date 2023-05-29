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

variables {Ω F : Type*} [topological_space Ω] {m : measurable_space Ω} [mΩ : measurable_space Ω]
  [polish_space Ω] [borel_space Ω] [nonempty Ω]
  {μ : measure Ω} [is_finite_measure μ]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]

/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m`. -/
@[irreducible] noncomputable
def condexp_kernel (μ : measure Ω) [is_finite_measure μ] (m : measurable_space Ω) :
  @kernel Ω Ω m mΩ :=
@cond_distrib Ω Ω Ω _ mΩ _ _ _ mΩ m id id μ _

lemma ae_strongly_measurable_comp_snd_map_prod_mk (hm : m ≤ mΩ)
  {f : Ω → F} (hf_int : integrable f μ) :
  @ae_strongly_measurable (Ω × Ω) F _ (m.prod mΩ) (λ x : Ω × Ω, f x.2)
    (@measure.map _ _ (m.prod mΩ) _ (λ ω, (ω, ω)) μ) :=
begin
  let f' := hf_int.1.mk f,
  refine ⟨λ x, f' x.2, hf_int.1.strongly_measurable_mk.comp_measurable measurable_snd, _⟩,
  suffices h : @measure.quasi_measure_preserving (Ω × Ω) Ω mΩ (m.prod mΩ) prod.snd
    (@measure.map _ _ (m.prod mΩ) _ (λ ω, (ω, ω)) μ) μ,
  { exact measure.quasi_measure_preserving.ae_eq h hf_int.1.ae_eq_mk, },
  refine ⟨measurable_snd, measure.absolutely_continuous.mk (λ s hs hμs, _)⟩,
  rw measure.map_apply _ hs,
  swap, { exact measurable_snd, },
  rw measure.map_apply,
  { rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id'],
    exact hμs, },
  { exact (measurable_id.mono hm le_rfl).prod_mk measurable_id, },
  { exact measurable_snd hs, },
end

lemma integrable_comp_snd_map_prod_mk (hm : m ≤ mΩ) {f : Ω → F} (hf_int : integrable f μ) :
  @integrable F _ (Ω × Ω) (m.prod mΩ) (λ x : Ω × Ω, f x.2)
    (@measure.map _ _ (m.prod mΩ) _ (λ ω, (ω, ω)) μ) :=
begin
  have hX : @measurable Ω Ω mΩ m id := measurable_id.mono le_rfl hm,
  have hY : measurable (id : Ω → Ω) := measurable_id,
  have hXY : @ae_measurable Ω (Ω × Ω) (m.prod mΩ) mΩ (λ ω, (ω, ω)) μ :=
    @measurable.ae_measurable Ω (Ω × Ω) mΩ (m.prod mΩ) _ μ (hX.prod_mk hY),
  have hf := ae_strongly_measurable_comp_snd_map_prod_mk hm hf_int,
  refine ⟨hf, _⟩,
  rw [has_finite_integral, lintegral_map' hf.ennnorm hXY],
  exact hf_int.2,
end

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condexp_kernel μ m ω)`. -/
lemma condexp_ae_eq_integral_condexp_kernel (hm : m ≤ mΩ) {f : Ω → F} (hf_int : integrable f μ) :
  μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω) :=
begin
  have hX : @measurable Ω Ω mΩ m id := measurable_id.mono le_rfl hm,
  have hY : ae_measurable (id : Ω → Ω) μ := ae_measurable_id,
  have hf_int' : @integrable F _ (Ω × Ω) (m.prod mΩ) (λ x : Ω × Ω, f x.2)
    (@measure.map _ _ (m.prod mΩ) _ (λ ω, (ω, ω)) μ),
  { exact integrable_comp_snd_map_prod_mk hm hf_int, },
  rw condexp_kernel,
  refine eventually_eq.trans _ (condexp_prod_ae_eq_integral_cond_distrib' hX hY hf_int'),
  simp only [measurable_space.comap_id, id.def],
end

end probability_theory

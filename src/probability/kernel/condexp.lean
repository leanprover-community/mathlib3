/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.cond_distrib

/-!
# Kernel associated with a conditional expectation

We define `condexp_kernel μ m`, a kernel from `Ω` to `Ω` such that for all integrable, strongly
measurable `f`, `μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω)`.

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

/-- Kernel associated with the conditional expectation with respect to a σ-algebra. -/
@[irreducible] noncomputable
def condexp_kernel (μ : measure Ω) [is_finite_measure μ] (m : measurable_space Ω) :
  @kernel Ω Ω m mΩ :=
@cond_distrib Ω Ω Ω _ mΩ _ _ _ mΩ m id id μ _

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condexp_kernel μ m ω)`. -/
lemma condexp_ae_eq_integral_condexp_kernel (hm : m ≤ mΩ)
  {f : Ω → F} (hf : strongly_measurable f) (hf_int : integrable f μ) :
  μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω) :=
begin
  have hX : @measurable Ω Ω mΩ m id := measurable_id.mono le_rfl hm,
  have hY : ae_measurable (id : Ω → Ω) μ := ae_measurable_id,
  have hf' : @strongly_measurable (Ω × Ω) F _ (m.prod mΩ) (λ x : Ω × Ω, f x.2) :=
    hf.comp_measurable measurable_id.snd,
  rw condexp_kernel,
  refine eventually_eq.trans _ (condexp_prod_ae_eq_integral_cond_distrib hX hY hf' hf_int),
  simp only [measurable_space.comap_id, id.def],
end

end probability_theory

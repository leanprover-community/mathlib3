/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import measure_theory.ae_eq_fun

/-!
# Emetric space structure on almost everywhere equal functions

Emetric on `L⁰` :
    If `β` is an `emetric_space`, then `L⁰` can be made into an `emetric_space`, where
    `edist [f] [g]` is defined to be `∫⁻ a, edist (f a) (g a)`.

    The integral used here is `lintegral : (α → ℝ≥0∞) → ℝ≥0∞`, which is defined in the file
    `integration.lean`.

    See `edist_mk_mk` and `edist_to_fun`.

TODO: remove this file, and use instead the more general `Lp` space specialized to `p = 1`.
-/

noncomputable theory
open_locale classical ennreal

open set filter topological_space ennreal emetric measure_theory function
variables {α β γ δ : Type*} [measurable_space α] {μ ν : measure α}

namespace measure_theory

namespace ae_eq_fun
variables [measurable_space β] [measurable_space γ] [measurable_space δ]

section
variables [emetric_space γ] [second_countable_topology γ] [opens_measurable_space γ]

/-- `comp_edist [f] [g] a` will return `edist (f a) (g a)` -/
protected def edist (f g : α →ₘ[μ] γ) : α →ₘ[μ] ℝ≥0∞ := comp₂ edist measurable_edist f g

protected lemma edist_comm (f g : α →ₘ[μ] γ) : f.edist g = g.edist f :=
induction_on₂ f g $ λ f hf g hg, mk_eq_mk.2 $ eventually_of_forall $ λ x, edist_comm (f x) (g x)

lemma coe_fn_edist (f g : α →ₘ[μ] γ) : ⇑(f.edist g) =ᵐ[μ] λ a, edist (f a) (g a) :=
coe_fn_comp₂ _ _ _ _

protected lemma edist_self (f : α →ₘ[μ] γ) : f.edist f = 0 :=
induction_on f $ λ f hf, mk_eq_mk.2 $ eventually_of_forall $ λ x, edist_self (f x)

/-- Almost everywhere equal functions form an `emetric_space`, with the emetric defined as
  `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
instance : emetric_space (α →ₘ[μ] γ) :=
{ edist               := λf g, lintegral (f.edist g),
  edist_self          := assume f, lintegral_eq_zero_iff.2 f.edist_self,
  edist_comm          := λ f g, congr_arg lintegral $ f.edist_comm g,
  edist_triangle      := λ f g h, induction_on₃ f g h $ λ f hf g hg h hh,
    calc ∫⁻ a, edist (f a) (h a) ∂μ ≤ ∫⁻ a, edist (f a) (g a) + edist (g a) (h a) ∂μ :
      measure_theory.lintegral_mono (λ a, edist_triangle (f a) (g a) (h a))
    ... = ∫⁻ a, edist (f a) (g a) ∂μ + ∫⁻ a, edist (g a) (h a) ∂μ :
      lintegral_add' (hf.edist hg) (hg.edist hh),
  eq_of_edist_eq_zero := λ f g, induction_on₂ f g $ λ f hf g hg H, mk_eq_mk.2 $
    ((lintegral_eq_zero_iff' (hf.edist hg)).1 H).mono $ λ x, eq_of_edist_eq_zero }

lemma edist_mk_mk {f g : α → γ} (hf hg) :
  edist (mk f hf : α →ₘ[μ] γ) (mk g hg) = ∫⁻ x, edist (f x) (g x) ∂μ :=
rfl

lemma edist_eq_coe (f g : α →ₘ[μ] γ) : edist f g = ∫⁻ x, edist (f x) (g x) ∂μ :=
by rw [← edist_mk_mk, mk_coe_fn, mk_coe_fn]

lemma edist_zero_eq_coe [has_zero γ] (f : α →ₘ[μ] γ) : edist f 0 = ∫⁻ x, edist (f x) 0 ∂μ :=
by rw [← edist_mk_mk, mk_coe_fn, zero_def]

end

section metric
variables [metric_space γ] [second_countable_topology γ] [opens_measurable_space γ]

lemma edist_mk_mk' {f g : α → γ} (hf hg) :
  edist (mk f hf : α →ₘ[μ] γ) (mk g hg) = ∫⁻ x, nndist (f x) (g x) ∂μ :=
by simp only [edist_mk_mk, edist_nndist]

lemma edist_eq_coe' (f g : α →ₘ[μ] γ) : edist f g = ∫⁻ x, nndist (f x) (g x) ∂μ :=
by simp only [edist_eq_coe, edist_nndist]

end metric

lemma edist_add_right [normed_group γ] [second_countable_topology γ] [borel_space γ]
  (f g h : α →ₘ[μ] γ) :
  edist (f + h) (g + h) = edist f g :=
induction_on₃ f g h $ λ f hf g hg h hh, by simp [edist_mk_mk, edist_dist, dist_add_right]

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜]
variables [normed_group γ] [second_countable_topology γ] [normed_space 𝕜 γ] [borel_space γ]

lemma edist_smul (c : 𝕜) (f : α →ₘ[μ] γ) : edist (c • f) 0 = (ennreal.of_real ∥c∥) * edist f 0 :=
induction_on f $ λ f hf, by simp [edist_mk_mk, zero_def, smul_mk, edist_dist, norm_smul,
  ennreal.of_real_mul, lintegral_const_mul']

end normed_space

end ae_eq_fun

end measure_theory

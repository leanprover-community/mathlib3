/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.l1_space
import measure_theory.function.strongly_measurable.inner

/-! # `ℒᵖ` and `ℒ¹` properties for inner-product-space operations -/

open_locale ennreal
open filter

namespace measure_theory
variables {α : Type*} {m : measurable_space α} {p : ℝ≥0∞} {μ : measure α}

variables {E 𝕜 : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

lemma mem_ℒp.const_inner (c : E) {f : α → E} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ a, ⟪c, f a⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner ae_strongly_measurable_const hf.1)
  (eventually_of_forall (λ x, norm_inner_le_norm _ _))

lemma mem_ℒp.inner_const {f : α → E} (hf : mem_ℒp f p μ) (c : E) :
  mem_ℒp (λ a, ⟪f a, c⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner hf.1 ae_strongly_measurable_const)
  (eventually_of_forall (λ x, by { rw mul_comm, exact norm_inner_le_norm _ _, }))

variables {f : α → E}

lemma integrable.const_inner (c : E) (hf : integrable f μ) : integrable (λ x, ⟪c, f x⟫) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.const_inner c, }

lemma integrable.inner_const (hf : integrable f μ) (c : E) : integrable (λ x, ⟪f x, c⟫) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.inner_const c, }

end measure_theory

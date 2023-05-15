/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.lp_space.basic
import measure_theory.function.strongly_measurable.inner

/-! # Behaviour of membership in `ℒᵖ` under inner-product-space and `is_R_or_C1 operations -/

open_locale ennreal
open filter

namespace measure_theory
variables {α : Type*} {m : measurable_space α} {p : ℝ≥0∞} {μ : measure α}

section is_R_or_C
variables {𝕜 : Type*} [is_R_or_C 𝕜] {f : α → 𝕜}

lemma mem_ℒp.re (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.re (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.re (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_re_le_norm (f x), },
  exact hf.of_le_mul hf.1.re (eventually_of_forall this),
end

lemma mem_ℒp.im (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.im (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.im (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_im_le_norm (f x), },
  exact hf.of_le_mul hf.1.im (eventually_of_forall this),
end

end is_R_or_C

section inner_product
variables {E' 𝕜 : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E'] [inner_product_space 𝕜 E']

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E' _ x y

lemma mem_ℒp.const_inner (c : E') {f : α → E'} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ a, ⟪c, f a⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner ae_strongly_measurable_const hf.1)
  (eventually_of_forall (λ x, norm_inner_le_norm _ _))

lemma mem_ℒp.inner_const {f : α → E'} (hf : mem_ℒp f p μ) (c : E') :
  mem_ℒp (λ a, ⟪f a, c⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner hf.1 ae_strongly_measurable_const)
  (eventually_of_forall (λ x, by { rw mul_comm, exact norm_inner_le_norm _ _, }))

end inner_product

section is_R_or_C

variables {K : Type*} [is_R_or_C K]

lemma mem_ℒp.of_real
  {f : α → ℝ} (hf : mem_ℒp f p μ) : mem_ℒp (λ x, (f x : K)) p μ :=
(@is_R_or_C.of_real_clm K _).comp_mem_ℒp' hf

lemma mem_ℒp_re_im_iff {f : α → K} :
  mem_ℒp (λ x, is_R_or_C.re (f x)) p μ ∧ mem_ℒp (λ x, is_R_or_C.im (f x)) p μ ↔
  mem_ℒp f p μ :=
begin
  refine ⟨_, λ hf, ⟨hf.re, hf.im⟩⟩,
  rintro ⟨hre, him⟩,
  convert hre.of_real.add (him.of_real.const_mul is_R_or_C.I),
  { ext1 x,
    rw [pi.add_apply, mul_comm, is_R_or_C.re_add_im] },
  all_goals { apply_instance }
end

end is_R_or_C

end measure_theory

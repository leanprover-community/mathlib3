/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability_theory.density

/-
Right now, pdf is defined such that `μ.with_density f` must agree with
`map X ℙ` everywhere, while in introductory probability courses, is condition
is often relaxed such that they only need to agree on intervals of the form `(-∞, x]`.
While, these conditions are not equivalent in general, for finite measures, it is the case.

pf. Use Dykin's π-λ theorem.

With that in mind, we can show that if `F(x) := map X ℙ (-∞, x]` is differentiable,
by FTC `f := F'` satisfies `∫ x in a..b, f x ∂μ = F b - F a = map X ℙ (a, b]`, hence, implying
`μ.with_density f` equals `map X ℙ` and thus, `f =ᵐ[μ] pdf X`.

This allows us to use traditional methods for find the pdf of transformations, namely
`pdf g(X) x = pdf X (g⁻¹ x) * g'`.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal interval

namespace measure_theory

open set topological_space measurable_space measure

-- variables {α E F : Type*}
-- variables [normed_group E] [measurable_space E] [second_countable_topology E] [linear_order E]
--   [order_topology E] [normed_space ℝ E] [complete_space E] [borel_space E]
-- variables [normed_group F] [measurable_space F] [second_countable_topology F] [linear_order F]
--   [order_topology F] [normed_space ℝ F] [complete_space F] [borel_space F]
--   [linear_order F] [order_topology F]

#check ext_of_generate_finite
#check borel_eq_generate_Iio
#check ext_of_Iic

variables {α : Type*} [measurable_space α]
variables {𝕜 : Type*} [measurable_space 𝕜] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 ℝ]

def cdf [preorder 𝕜] (X : α → 𝕜) (ℙ : measure α) (x : 𝕜) :=
(map X ℙ (Iic x)).to_real

section

variables {ℙ : measure α} {μ : measure 𝕜}

variables [second_countable_topology 𝕜] [complete_space 𝕜] [borel_space 𝕜] [normed_space ℝ 𝕜]
  [linear_order 𝕜] [order_topology 𝕜]

lemma pdf_ae_eq_of_cdf (X : α → 𝕜) (h : differentiable ℝ (cdf X ℙ)) :
  (λ x, (pdf X ℙ μ x).to_real) =ᵐ[μ] deriv (cdf X ℙ) :=
begin
  sorry
end

end

end measure_theory

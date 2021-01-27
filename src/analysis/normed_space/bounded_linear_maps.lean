/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import analysis.normed_space.multilinear

noncomputable theory
open_locale classical big_operators topological_space

open filter (tendsto)
open metric

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]

section
variables {ι : Type*} [decidable_eq ι] [fintype ι]

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
lemma is_bounded_linear_map_continuous_multilinear_map_comp_linear (g : G →L[𝕜] E) :
  is_bounded_linear_map 𝕜 (λ f : continuous_multilinear_map 𝕜 (λ (i : ι), E) F,
    f.comp_continuous_linear_map (λ _, g)) :=
begin
  refine is_linear_map.with_bound ⟨λ f₁ f₂, by { ext m, refl }, λ c f, by { ext m, refl }⟩
    (∥g∥ ^ (fintype.card ι)) (λ f, _),
  apply continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _),
  { apply_rules [mul_nonneg, pow_nonneg, norm_nonneg] },
  calc ∥f (g ∘ m)∥ ≤
    ∥f∥ * ∏ i, ∥g (m i)∥ : f.le_op_norm _
    ... ≤ ∥f∥ * ∏ i, (∥g∥ * ∥m i∥) : begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      exact finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, g.le_op_norm _)
    end
    ... = ∥g∥ ^ fintype.card ι * ∥f∥ * ∏ i, ∥m i∥ :
      by { simp [finset.prod_mul_distrib, finset.card_univ], ring }
end

end

section bilinear_map

variable (𝕜)

variable {𝕜}
variable {f : E × F → G}

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
lemma is_bounded_bilinear_map_comp_multilinear {ι : Type*} {E : ι → Type*}
[decidable_eq ι] [fintype ι] [∀i, normed_group (E i)] [∀i, normed_space 𝕜 (E i)] :
  is_bounded_bilinear_map 𝕜 (λ p : (F →L[𝕜] G) × (continuous_multilinear_map 𝕜 E F),
    p.1.comp_continuous_multilinear_map p.2) :=
{ add_left   := λ g₁ g₂ f, by { ext m, refl },
  smul_left  := λ c g f, by { ext m, refl },
  add_right  := λ g f₁ f₂, by { ext m, simp },
  smul_right := λ c g f, by { ext m, simp },
  bound      := ⟨1, zero_lt_one, λ g f, begin
    apply continuous_multilinear_map.op_norm_le_bound _ _ (λm, _),
    { apply_rules [mul_nonneg, zero_le_one, norm_nonneg] },
    calc ∥g (f m)∥ ≤ ∥g∥ * ∥f m∥ : g.le_op_norm _
    ... ≤ ∥g∥ * (∥f∥ * ∏ i, ∥m i∥) :
      mul_le_mul_of_nonneg_left (f.le_op_norm _) (norm_nonneg _)
    ... = 1 * ∥g∥ * ∥f∥ * ∏ i, ∥m i∥ : by ring
    end⟩ }

end bilinear_map

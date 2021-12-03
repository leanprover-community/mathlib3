/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability_theory.stopping
import measure_theory.function.conditional_expectation

/-! # Martingales

-/

open topological_space filter
open_locale nnreal ennreal measure_theory

namespace measure_theory

variables {α E ι : Type*} [preorder ι] [measurable_space E]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [second_countable_topology E]
  {f g : ι → α → E} {ℱ : filtration ι m0} [sigma_finite_filtration μ ℱ]

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] =ᵐ[μ] f i`. -/
def is_martingale (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
(∀ i, integrable (f i) μ) ∧ (adapted ℱ f) ∧ ∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i

lemma is_martingale.integrable (hf : is_martingale f ℱ μ) : ∀ i, integrable (f i) μ := hf.1

lemma is_martingale.adapted (hf : is_martingale f ℱ μ) : adapted ℱ f := hf.2.1

lemma is_martingale.add (hf : is_martingale f ℱ μ) (hg : is_martingale g ℱ μ) :
  is_martingale (f + g) ℱ μ :=
begin
  refine ⟨λ i, (hf.integrable i).add (hg.integrable i), hf.adapted.add hg.adapted, λ i j hij, _⟩,
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans
    ((hf.2.2 i j hij).add (hg.2.2 i j hij)),
end

lemma is_martingale.neg (hf : is_martingale f ℱ μ) : is_martingale (-f) ℱ μ :=
begin
  refine ⟨λ i, (hf.integrable i).neg, hf.adapted.neg, λ i j hij, _⟩,
  exact (condexp_neg (f j)).trans ((hf.2.2 i j hij).neg),
end

lemma is_martingale.sub (hf : is_martingale f ℱ μ) (hg : is_martingale g ℱ μ) :
  is_martingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg, }

lemma is_martingale.smul (c : ℝ) (hf : is_martingale f ℱ μ) : is_martingale (c • f) ℱ μ :=
begin
  refine ⟨λ i, (hf.integrable i).smul c, hf.adapted.smul c, λ i j hij, _⟩,
  refine (condexp_smul c (f j)).trans _,
  refine (hf.2.2 i j hij).mono (λ x hx, _),
  rw [pi.smul_apply, hx, pi.smul_apply, pi.smul_apply],
end

variables (E)
lemma is_martingale_zero (ℱ : filtration ι m0) (μ : measure α) [sigma_finite_filtration μ ℱ] :
  is_martingale (0 : ι → α → E) ℱ μ :=
⟨λ i, integrable_zero _ _ _, adapted_zero E ℱ,
  λ i j hij, by { rw [pi.zero_apply, condexp_zero], simp, }⟩

/-- TODO: submodule instead? -/
def martingale (ℱ : filtration ι m0) (μ : measure α) [sigma_finite_filtration μ ℱ] :
  add_subgroup (ι → α → E) :=
{ carrier   := {f | is_martingale f ℱ μ},
  zero_mem' := is_martingale_zero E ℱ μ,
  add_mem'  := λ f g, is_martingale.add,
  neg_mem'  := λ f, is_martingale.neg, }
variables {E}

/-- The martingale with value `μ[f | ℱ.le i]` for all `i ∈ E`. -/
noncomputable def to_martingale (f : α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] :
  martingale E ℱ μ :=
{ val := λ i, μ[f | ℱ i, ℱ.le i],
  property := ⟨λ i, integrable_condexp, λ i, measurable_condexp,
    λ i j hij, condexp_condexp_of_le (ℱ.mono hij) _⟩, }

end measure_theory

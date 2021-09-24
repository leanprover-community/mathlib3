/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.conditional_expectation

/-! # Filtrations and martingales

-/

open topological_space filter
open_locale nnreal ennreal measure_theory

namespace measure_theory

structure filtration {α} (ι) [preorder ι] {m0 : measurable_space α} (μ : measure α) :=
(map : ι → measurable_space α)
(le : ∀ i, map i ≤ m0)
(mono : monotone map)
(sigma_finite : ∀ i, sigma_finite (μ.trim (le i)))

variables {α E ι : Type*} [preorder ι] [measurable_space E]
  {m0 : measurable_space α} {μ : measure α}

/-- A family of functions `f` is adapted with respect to a filtration `ℱ` if for all `i`, `f i`
is `ℱ i`-measurable. -/
def adapted (f : ι → α → E) (ℱ : filtration ι μ) : Prop :=
∀ i, measurable[ℱ.map i] (f i)

lemma adapted.add [has_add E] [has_measurable_add₂ E] {f g : ι → α → E} {ℱ : filtration ι μ}
  (hf : adapted f ℱ) (hg : adapted g ℱ) :
  adapted (f + g) ℱ :=
λ i, @measurable.add _ _ _ _ (ℱ.map i) _ _ _ (hf i) (hg i)

lemma adapted.neg [has_neg E] [has_measurable_neg E] {f : ι → α → E} {ℱ : filtration ι μ}
  (hf : adapted f ℱ) :
  adapted (-f) ℱ :=
λ i, @measurable.neg _ α _ _ _ (ℱ.map i) _ (hf i)

lemma adapted.smul [has_scalar ℝ E] [has_measurable_smul ℝ E] {f : ι → α → E} {ℱ : filtration ι μ}
  (c : ℝ) (hf : adapted f ℱ) :
  adapted (c • f) ℱ :=
λ i, @measurable.const_smul ℝ E α _ _ _ (ℱ.map i) _ _ (hf i) c

variables (E)
lemma adapted_zero [has_zero E] (ℱ : filtration ι μ) : adapted (0 : ι → α → E) ℱ :=
λ i, @measurable_zero E α _ (ℱ.map i) _
variables {E}

variables [normed_group E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [second_countable_topology E]
  {f g : ι → α → E} {ℱ : filtration ι μ}

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] =ᵐ[μ] f i`. -/
def is_martingale (f : ι → α → E) (ℱ : filtration ι μ) : Prop :=
(∀ i, integrable (f i) μ) ∧ (adapted f ℱ) ∧
∀ i j, i ≤ j → by { haveI : sigma_finite (μ.trim (ℱ.le i)) := ℱ.sigma_finite i,
  exact μ[f j | ℱ.le i] =ᵐ[μ] f i, }

lemma is_martingale.integrable (hf : is_martingale f ℱ) : ∀ i, integrable (f i) μ := hf.1

lemma is_martingale.adapted (hf : is_martingale f ℱ) : adapted f ℱ := hf.2.1

lemma is_martingale.add (hf : is_martingale f ℱ) (hg : is_martingale g ℱ) :
  is_martingale (f + g) ℱ :=
begin
  refine ⟨λ i, (hf.integrable i).add (hg.integrable i), hf.adapted.add hg.adapted, λ i j hij, _⟩,
  haveI : sigma_finite (μ.trim (ℱ.le i)), from ℱ.sigma_finite i,
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans
    ((hf.2.2 i j hij).add (hg.2.2 i j hij)),
end

lemma is_martingale.neg (hf : is_martingale f ℱ) : is_martingale (-f) ℱ :=
begin
  refine ⟨λ i, (hf.integrable i).neg, hf.adapted.neg, λ i j hij, _⟩,
  haveI : sigma_finite (μ.trim (ℱ.le i)), from ℱ.sigma_finite i,
  exact (condexp_neg (f j)).trans ((hf.2.2 i j hij).neg),
end

lemma is_martingale.sub (hf : is_martingale f ℱ) (hg : is_martingale g ℱ) :
  is_martingale (f - g) ℱ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg, }

lemma is_martingale.smul (c : ℝ) (hf : is_martingale f ℱ) : is_martingale (c • f) ℱ :=
begin
  refine ⟨λ i, (hf.integrable i).smul c, hf.adapted.smul c, λ i j hij, _⟩,
  haveI : sigma_finite (μ.trim (ℱ.le i)), from ℱ.sigma_finite i,
  refine (condexp_smul c (f j)).trans _,
  refine (hf.2.2 i j hij).mono (λ x hx, _),
  rw [pi.smul_apply, hx, pi.smul_apply, pi.smul_apply],
end

variables (E)
lemma is_martingale_zero (ℱ : filtration ι μ) : is_martingale (0 : ι → α → E) ℱ  :=
⟨λ i, integrable_zero _ _ _, adapted_zero E ℱ,
  λ i j hij, by { rw [pi.zero_apply, condexp_zero], simp, }⟩

/-- TODO: submodule instead? -/
def martingale (ℱ : filtration ι μ) : add_subgroup (ι → α → E) :=
{ carrier   := {f | is_martingale f ℱ},
  zero_mem' := is_martingale_zero E ℱ,
  add_mem'  := λ f g, is_martingale.add,
  neg_mem'  := λ f, is_martingale.neg, }
variables {E}

/-- The martingale with value `μ[f | ℱ.le i]` for all `i ∈ E`. -/
noncomputable def to_martingale (f : α → E) (ℱ : filtration ι μ) : martingale E ℱ :=
{ val := λ i,
    by { haveI : sigma_finite (μ.trim (ℱ.le i)) := ℱ.sigma_finite i, exact μ[f | ℱ.le i], },
  property :=
  begin
    refine ⟨λ i, _, λ i, _, λ i j hij, _⟩,
    { haveI : sigma_finite (μ.trim (ℱ.le i)), from ℱ.sigma_finite i,
      exact integrable_condexp, },
    { haveI : sigma_finite (μ.trim (ℱ.le i)), from ℱ.sigma_finite i,
      exact measurable_condexp, },
    { haveI : sigma_finite (μ.trim (ℱ.le i)), from ℱ.sigma_finite i,
      haveI : sigma_finite (μ.trim (ℱ.le j)), from ℱ.sigma_finite j,
      exact condexp_condexp_of_le (ℱ.mono hij) _, },
  end }

end measure_theory

/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability_theory.stopping
import measure_theory.function.conditional_expectation

/-!
# Martingales

A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] =ᵐ[μ] f i`.
The definitions of filtration and adapted can be found in `probability_theory.stopping`.

### Definitions

* `measure_theory.martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `measure_theory.martingale_condexp f ℱ μ`: the sequence `λ i, μ[f | ℱ i, ℱ.le i])` is a
  martingale with respect to `ℱ` and `μ`.

-/

open topological_space filter
open_locale nnreal ennreal measure_theory

namespace measure_theory

variables {α E ι : Type*} [preorder ι] [measurable_space E]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [second_countable_topology E]
  {f g : ι → α → E} {ℱ : filtration ι m0} [sigma_finite_filtration μ ℱ]

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ.le i] =ᵐ[μ] f i`. -/
def martingale (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i

def supermartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] ≤ᵐ[μ] f i) ∧ ∀ i, integrable (f i) μ

def submartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i, ℱ.le i]) ∧ ∀ i, integrable (f i) μ

variables (E)
lemma martingale_zero (ℱ : filtration ι m0) (μ : measure α) [sigma_finite_filtration μ ℱ] :
  martingale (0 : ι → α → E) ℱ μ :=
⟨adapted_zero E ℱ, λ i j hij, by { rw [pi.zero_apply, condexp_zero], simp, }⟩
variables {E}

namespace martingale

lemma adapted (hf : martingale f ℱ μ) : adapted ℱ f := hf.1

lemma measurable (hf : martingale f ℱ μ) (i : ι) : measurable[ℱ i] (f i) := hf.adapted i

lemma condexp_ae_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i :=
hf.2 i j hij

lemma integrable (hf : martingale f ℱ μ) (i : ι) : integrable (f i) μ :=
integrable_condexp.congr (hf.condexp_ae_eq (le_refl i))

lemma set_integral_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) {s : set α}
  (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ :=
begin
  rw ← @set_integral_condexp _ _ _ _ _ _ _ _ (ℱ i) m0 _ (ℱ.le i) _ _ _ (hf.integrable j) hs,
  refine set_integral_congr_ae (ℱ.le i s hs) _,
  filter_upwards [hf.2 i j hij],
  intros _ heq _,
  exact heq.symm,
end

lemma add (hf : martingale f ℱ μ) (hg : martingale g ℱ μ) : martingale (f + g) ℱ μ :=
begin
  refine ⟨hf.adapted.add hg.adapted, λ i j hij, _⟩,
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans
    ((hf.2 i j hij).add (hg.2 i j hij)),
end

lemma neg (hf : martingale f ℱ μ) : martingale (-f) ℱ μ :=
⟨hf.adapted.neg, λ i j hij, (condexp_neg (f j)).trans ((hf.2 i j hij).neg)⟩

lemma sub (hf : martingale f ℱ μ) (hg : martingale g ℱ μ) : martingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg, }

lemma smul (c : ℝ) (hf : martingale f ℱ μ) : martingale (c • f) ℱ μ :=
begin
  refine ⟨hf.adapted.smul c, λ i j hij, _⟩,
  refine (condexp_smul c (f j)).trans ((hf.2 i j hij).mono (λ x hx, _)),
  rw [pi.smul_apply, hx, pi.smul_apply, pi.smul_apply],
end

lemma supermartingale [preorder E] (hf : martingale f ℱ μ) : supermartingale f ℱ μ :=
⟨hf.1, λ i j hij, (hf.2 i j hij).le, λ i, hf.integrable i⟩

lemma submartingale [preorder E] (hf : martingale f ℱ μ) : submartingale f ℱ μ :=
⟨hf.1, λ i j hij, (hf.2 i j hij).symm.le, λ i, hf.integrable i⟩

end martingale

lemma martingale_iff [partial_order E] : martingale f ℱ μ ↔
  supermartingale f ℱ μ ∧ submartingale f ℱ μ :=
⟨λ hf, ⟨hf.supermartingale, hf.submartingale⟩,
 λ ⟨hf₁, hf₂⟩, ⟨hf₁.1, λ i j hij, (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

lemma martingale_condexp (f : α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] :
  martingale (λ i, μ[f | ℱ i, ℱ.le i]) ℱ μ :=
⟨λ i, measurable_condexp, λ i j hij, condexp_condexp_of_le (ℱ.mono hij) _⟩

namespace supermartingale

lemma adapted [has_le E] (hf : supermartingale f ℱ μ) : adapted ℱ f := hf.1

lemma measurable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) : measurable[ℱ i] (f i) :=
hf.adapted i

lemma integrable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma condexp_ae_eq [has_le E] (hf : supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i, ℱ.le i] ≤ᵐ[μ] f i :=
hf.2.1 i j hij

lemma add [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : supermartingale g ℱ μ) : supermartingale (f + g) ℱ μ :=
begin
  refine ⟨hf.1.add hg.1, λ i j hij, _, λ i, (hf.2.2 i).add (hg.2.2 i)⟩,
  refine (condexp_add (hf.integrable j) (hg.integrable j)).le.trans _,
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij],
  intros,
  refine add_le_add _ _; assumption,
end

lemma add_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : martingale g ℱ μ) : supermartingale (f + g) ℱ μ :=
hf.add hg.supermartingale

lemma neg [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) : submartingale (-f) ℱ μ :=
begin
  refine ⟨hf.1.neg, λ i j hij, _, λ i, (hf.2.2 i).neg⟩,
  refine eventually_le.trans _ (condexp_neg (f j)).symm.le,
  filter_upwards [hf.2.1 i j hij],
  intros _ hle,
  simpa,
end

-- section

-- variables {F : Type*} [measurable_space F]
--   [ordered_add_comm_monoid F]
--   [normed_group F] [normed_space ℝ F] [complete_space F] [borel_space F]
--   [second_countable_topology F] --[ordered_smul ℝ F]

-- noncomputable
-- instance : mul_action_with_zero ℝ F :=
-- { smul := (•),
--   one_smul := one_smul ℝ,
--   mul_smul := mul_smul,
--   smul_zero := smul_zero,
--   zero_smul := zero_smul ℝ }

-- lemma smul_nonneg
--   {f : ι → α → F} {c : ℝ} (hc : 0 ≤ c) (hf : supermartingale f ℱ μ) :
--   supermartingale (c • f) ℱ μ :=
-- begin
--   refine ⟨hf.1.smul c, λ i j hij, _, λ i, (hf.2.2 i).smul c⟩,
--   refine (condexp_smul c (f j)).le.trans _,
--   filter_upwards [hf.2.1 i j hij],
--   intros _ hle,
--   have := @smul_le_smul_of_nonneg hle hc,
-- end

-- end

end supermartingale

end measure_theory

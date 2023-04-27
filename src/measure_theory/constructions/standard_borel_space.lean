/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.constructions.borel_isomorphism
import data.real.cardinality

/-!
# Standard Borel Space

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open set

namespace measure_theory

variables {α β : Type*}

instance {α : Type*} [topological_space α] [polish_space α] : polish_space (univ : set α) :=
is_closed.polish_space is_closed_univ

lemma exists_subset_real_measurable_equiv_of_finite (α)
  [topological_space α] [measurable_space α] [polish_space α] [borel_space α] [finite α] :
  ∃ n : ℕ, nonempty (α ≃ᵐ range (coe : fin n → ℝ)) :=
begin
  obtain ⟨n, ⟨n_equiv⟩⟩ := finite.exists_equiv_fin α,
  refine ⟨n, ⟨equiv.measurable_equiv (n_equiv.trans _)⟩⟩,
  exact equiv.of_injective _ (nat.cast_injective.comp fin.val_injective),
end

lemma exists_subset_real_measurable_equiv_of_infinite_of_countable (α)
  [topological_space α] [measurable_space α] [polish_space α] [borel_space α]
  [infinite α] [countable α] :
  nonempty (α ≃ᵐ range (coe : ℕ → ℝ)) :=
begin
  haveI : polish_space (range (coe : ℕ → ℝ)),
  { refine is_closed.polish_space _,
    refine is_closed_map.closed_range _,
    exact nat.closed_embedding_coe_real.is_closed_map, },
  refine ⟨equiv.measurable_equiv _⟩,
  refine (nonempty_equiv_of_countable.some : α ≃ ℕ).trans _,
  exact equiv.of_injective coe nat.cast_injective,
end

lemma exists_subset_real_measurable_equiv (α)
  [topological_space α] [measurable_space α] [polish_space α] [borel_space α] :
  ∃ s : set ℝ, nonempty (α ≃ᵐ s) :=
begin
  by_cases hα : countable α; haveI := hα,
  { casesI finite_or_infinite α with h h,
    { obtain ⟨n, h_nonempty_equiv⟩ := exists_subset_real_measurable_equiv_of_finite α,
      exact ⟨_, h_nonempty_equiv⟩, },
    { exact ⟨_, exists_subset_real_measurable_equiv_of_infinite_of_countable α⟩, }, },
  { refine ⟨univ, ⟨(measurable_equiv_of_uncountable hα _ : α ≃ᵐ (univ : set ℝ))⟩⟩,
    rw countable_coe_iff,
    exact cardinal.not_countable_real, }
end


end measure_theory

/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure.lebesgue
import measure_theory.measure.haar

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ`.
-/

open topological_space set

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.Icc01 : positive_compacts ℝ :=
⟨Icc 0 1, is_compact_Icc, by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

namespace measure_theory

open measure topological_space.positive_compacts

lemma is_add_left_invariant_real_volume : is_add_left_invariant ⇑(volume : measure ℝ) :=
by simp [← map_add_left_eq_self, real.map_volume_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
lemma haar_measure_eq_lebesgue_measure : add_haar_measure Icc01 = volume :=
begin
  convert (add_haar_measure_unique _ Icc01).symm,
  { simp [Icc01] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume }
end

class is_real_additive_haar_measure {E : Type*} [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] [measurable_space E] [borel_space E] (μ : measure E) : Prop :=
{ is_haar : ∃ (K : positive_compacts E), μ = add_haar_measure K }

instance : is_real_additive_haar_measure (volume : measure ℝ) :=
{ is_haar := ⟨Icc01, haar_measure_eq_lebesgue_measure.symm⟩ }

lemma map_is_real_additive_haar_measure
  {E : Type*} [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] [measurable_space E] [borel_space E]
  {F : Type*} [normed_group F] [normed_space ℝ F]
  [finite_dimensional ℝ F] [measurable_space F] [borel_space F]
  (e : E ≃ₗ[ℝ] F) (μ : measure E) [hμ : is_real_additive_haar_measure μ] :
  is_real_additive_haar_measure (measure.map e μ) :=
begin
  have Z : ∃ (K : positive_compacts E), μ = add_haar_measure K := hμ.is_haar,
  unfreezingI { rcases Z with ⟨K, rfl⟩ },
end


#exit

end measure_theory

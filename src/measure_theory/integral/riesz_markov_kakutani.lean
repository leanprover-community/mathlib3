/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
import topology.continuous_function.bounded

/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove different versions of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for compact spaces, from which the statements about linear functionals
on bounded continuous functions or compactly supported functions on locally compact spaces follow.

To make use of the existing API, the measure is constructed from a content $ \lambda $ on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

noncomputable theory

open_locale bounded_continuous_function nnreal ennreal
open set function

variables {X : Type*} [topological_space X]

-- Let `Λ` be a positive linear functional on the space of continuous functions on `X`.
-- (Specifically, we consider only nonnegative functions, and require the functional to
-- have nonnegative values.)
variables (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

/-- For `K ⊆ X` compact, define `λ(K) = inf {Λf | 1≤f on K}`.
  This will be a content on `X`. -/
def riesz_content_aux : (topological_space.compacts X) → ℝ≥0 :=
λ K, Inf (Λ '' {f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x})

section riesz_monotone

lemma riesz_content_aux_test_set_nonempty (K : topological_space.compacts X) :
  (Λ '' {f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x}).nonempty :=
begin
  rw nonempty_image_iff,
  use (1 : X →ᵇ ℝ≥0),
  intros x x_in_K,
  simp only [bounded_continuous_function.coe_one, pi.one_apply],
end

lemma riesz_content_aux_mono {K₁ K₂ : topological_space.compacts X} (h : K₁ ≤ K₂) :
  riesz_content_aux Λ K₁ ≤ riesz_content_aux Λ K₂ :=
cInf_le_cInf (order_bot.bdd_below _) (riesz_content_aux_test_set_nonempty Λ K₂)
  (image_subset Λ (set_of_subset_set_of.mpr (λ f f_hyp x x_in_K₁, f_hyp x (h x_in_K₁))))

end riesz_monotone

section riesz_subadditive

lemma riesz_content_aux_le_test_function_evaluation {K : topological_space.compacts X}
  {f : X →ᵇ ℝ≥0} (h : ∀ x∈ K, (1 : ℝ≥0) ≤ f x ) :
  riesz_content_aux Λ K ≤ Λ f := cInf_le (order_bot.bdd_below _) ⟨f, ⟨h, rfl⟩⟩

lemma riesz_content_aux_exists_test_function (K : topological_space.compacts X)
  {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ (f : X →ᵇ ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < riesz_content_aux Λ K + ε :=
begin
  --choose a test function `f` s.t. `Λf = α < μ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_cInf_lt (riesz_content_aux_test_set_nonempty Λ K)
    (lt_add_of_pos_right (riesz_content_aux Λ K) εpos),
  refine ⟨f, f_hyp.left, _ ⟩,
  rw f_hyp.right,
  exact α_hyp,
end

lemma riesz_content_aux_sup_le (K1 K2 : topological_space.compacts X) :
  riesz_content_aux Λ (K1 ⊔ K2) ≤ riesz_content_aux Λ (K1) + riesz_content_aux Λ (K2) :=
begin
  apply nnreal.le_of_forall_pos_le_add,
  intros ε εpos,
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := riesz_content_aux_exists_test_function Λ K1
    (nnreal.half_pos εpos),
  obtain ⟨f2, f_test_function_K2⟩ := riesz_content_aux_exists_test_function Λ K2
    (nnreal.half_pos εpos),
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : (∀ x ∈ (K1 ⊔ K2), (1 : ℝ≥0) ≤ (f1 + f2) x),
  { rintros x (x_in_K1 | x_in_K2),
    { exact le_add_right (f_test_function_K1.left x x_in_K1) },
    { exact le_add_left (f_test_function_K2.left x x_in_K2) }},
  --use that `Λf` is an upper bound for `μ(K1⊔K2)`
  apply (riesz_content_aux_le_test_function_evaluation Λ f_test_function_union).trans (le_of_lt _),
  rw map_add,
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (add_lt_add f_test_function_K1.right f_test_function_K2.right) (le_of_eq _),
  rw [add_assoc, add_comm (ε/2), add_assoc, nnreal.add_halves ε, add_assoc],
end

end riesz_subadditive

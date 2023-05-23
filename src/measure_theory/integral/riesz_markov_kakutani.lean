/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
import topology.continuous_function.bounded
import topology.sets.compacts

/-!
#  Riesz–Markov–Kakutani representation theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file will prove different versions of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for compact spaces, from which the statements about linear functionals
on bounded continuous functions or compactly supported functions on locally compact spaces follow.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

noncomputable theory

open_locale bounded_continuous_function nnreal ennreal
open set function topological_space

variables {X : Type*} [topological_space X]
variables (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

/-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
`λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def riesz_content_aux : (compacts X) → ℝ≥0 :=
λ K, Inf (Λ '' {f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x})

section riesz_monotone

/-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
functions f on X such that `f ≥ 1` on K. -/
lemma riesz_content_aux_image_nonempty (K : compacts X) :
  (Λ '' {f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x}).nonempty :=
begin
  rw nonempty_image_iff,
  use (1 : X →ᵇ ℝ≥0),
  intros x x_in_K,
  simp only [bounded_continuous_function.coe_one, pi.one_apply],
end

/-- Riesz content λ (associated with a positive linear functional Λ) is
monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
lemma riesz_content_aux_mono {K₁ K₂ : compacts X} (h : K₁ ≤ K₂) :
  riesz_content_aux Λ K₁ ≤ riesz_content_aux Λ K₂ :=
cInf_le_cInf (order_bot.bdd_below _) (riesz_content_aux_image_nonempty Λ K₂)
  (image_subset Λ (set_of_subset_set_of.mpr (λ f f_hyp x x_in_K₁, f_hyp x (h x_in_K₁))))

end riesz_monotone

section riesz_subadditive

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
lemma riesz_content_aux_le {K : compacts X}
  {f : X →ᵇ ℝ≥0} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
  riesz_content_aux Λ K ≤ Λ f := cInf_le (order_bot.bdd_below _) ⟨f, ⟨h, rfl⟩⟩

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
lemma exists_lt_riesz_content_aux_add_pos (K : compacts X)
  {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ (f : X →ᵇ ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < riesz_content_aux Λ K + ε :=
begin
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_cInf_lt (riesz_content_aux_image_nonempty Λ K)
    (lt_add_of_pos_right (riesz_content_aux Λ K) εpos),
  refine ⟨f, f_hyp.left, _ ⟩,
  rw f_hyp.right,
  exact α_hyp,
end

/-- The Riesz content λ associated to a given positive linear functional Λ is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
lemma riesz_content_aux_sup_le (K1 K2 : compacts X) :
  riesz_content_aux Λ (K1 ⊔ K2) ≤ riesz_content_aux Λ (K1) + riesz_content_aux Λ (K2) :=
begin
  apply nnreal.le_of_forall_pos_le_add,
  intros ε εpos,
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_riesz_content_aux_add_pos Λ K1
    (half_pos εpos),
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_riesz_content_aux_add_pos Λ K2
    (half_pos εpos),
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : (∀ x ∈ (K1 ⊔ K2), (1 : ℝ≥0) ≤ (f1 + f2) x),
  { rintros x (x_in_K1 | x_in_K2),
    { exact le_add_right (f_test_function_K1.left x x_in_K1) },
    { exact le_add_left (f_test_function_K2.left x x_in_K2) }},
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (riesz_content_aux_le Λ f_test_function_union).trans (le_of_lt _),
  rw map_add,
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (add_lt_add f_test_function_K1.right f_test_function_K2.right) (le_of_eq _),
  rw [add_assoc, add_comm (ε/2), add_assoc, add_halves ε, add_assoc],
end

end riesz_subadditive

/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.exposed

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

def set.vertices (A : set E) :
  set E :=
{x | x ∈ frontier A ∧ ∀ w : E, w ≠ x → ((∃ l : E →L[ℝ] ℝ, l x ≤ l w ∧ ∀ y ∈ A, l y ≤ l x) →
  ∃ l : E →L[ℝ] ℝ, l x < l w ∧ ∀ y ∈ A, l y ≤ l x) ∧ ((∃ l : E →L[ℝ] ℝ, l x ≤ l w ∧ ∀ y ∈ Aᶜ,
  l y ≤ l x) → ∃ l : E →L[ℝ] ℝ, l x < l w ∧ ∀ y ∈ Aᶜ, l y ≤ l x)}

/-def set.vertices (A : set E) :
  set E :=
{x | x ∈ frontier A ∧ ∀ w : E, w ≠ x → (∃ l : E →L[ℝ] ℝ, l x ≤ l w ∧ ∀ y ∈ A, l y ≤ l x) →
  ∃ l : E →L[ℝ] ℝ, l x < l w ∧ ∀ y ∈ A, l y ≤ l x}-/

lemma contrapose :
  ∀ w : E, w ≠ x → (∃ l : E →L[ℝ] ℝ, l x ≤ l w ∧ ∀ y ∈ A, l y ≤ l x) →
  ∃ l : E →L[ℝ] ℝ, l x < l w ∧ ∀ y ∈ A, l y ≤ l x :=
begin
  by_contra,
  push_neg at h,
  sorry
end

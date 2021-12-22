/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.isometry
import topology.continuous_function.bounded
import topology.compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℝ)`.
-/

noncomputable theory

open set

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- The space of bounded sequences, with its sup norm -/
@[reducible] def ℓ_infty_ℝ : Type := bounded_continuous_function ℕ ℝ
open bounded_continuous_function metric topological_space

namespace Kuratowski_embedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/

variables {f g : ℓ_infty_ℝ} {n : ℕ} {C : ℝ} [metric_space α] (x : ℕ → α) (a b : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `Kuratowski_embedding`,
without density assumptions. -/
def embedding_of_subset : ℓ_infty_ℝ :=
of_normed_group_discrete (λn, dist a (x n) - dist (x 0) (x n)) (dist a (x 0))
  (λ_, abs_dist_sub_le _ _ _)

lemma embedding_of_subset_coe : embedding_of_subset x a n = dist a (x n) - dist (x 0) (x n) := rfl

/-- The embedding map is always a semi-contraction. -/
lemma embedding_of_subset_dist_le (a b : α) :
  dist (embedding_of_subset x a) (embedding_of_subset x b) ≤ dist a b :=
begin
  refine (dist_le dist_nonneg).2 (λn, _),
  simp only [embedding_of_subset_coe, real.dist_eq],
  convert abs_dist_sub_le a b (x n) using 2,
  ring
end

/-- When the reference set is dense, the embedding map is an isometry on its image. -/
lemma embedding_of_subset_isometry (H : dense_range x) : isometry (embedding_of_subset x) :=
begin
  refine isometry_emetric_iff_metric.2 (λa b, _),
  refine (embedding_of_subset_dist_le x a b).antisymm (le_of_forall_pos_le_add (λe epos, _)),
  /- First step: find n with dist a (x n) < e -/
  rcases metric.mem_closure_range_iff.1 (H a) (e/2) (half_pos epos) with ⟨n, hn⟩,
  /- Second step: use the norm control at index n to conclude -/
  have C : dist b (x n) - dist a (x n) = embedding_of_subset x b n - embedding_of_subset x a n :=
    by { simp only [embedding_of_subset_coe, sub_sub_sub_cancel_right] },
  have := calc
    dist a b ≤ dist a (x n) + dist (x n) b : dist_triangle _ _ _
    ...    = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) : by { simp [dist_comm], ring }
    ...    ≤ 2 * dist a (x n) + |dist b (x n) - dist a (x n)| :
      by apply_rules [add_le_add_left, le_abs_self]
    ...    ≤ 2 * (e/2) + |embedding_of_subset x b n - embedding_of_subset x a n| :
      begin rw C, apply_rules [add_le_add, mul_le_mul_of_nonneg_left, hn.le, le_refl], norm_num end
    ...    ≤ 2 * (e/2) + dist (embedding_of_subset x b) (embedding_of_subset x a) :
      by simp [← real.dist_eq, dist_coe_le_dist]
    ...    = dist (embedding_of_subset x b) (embedding_of_subset x a) + e : by ring,
  simpa [dist_comm] using this
end

/-- Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/
theorem exists_isometric_embedding (α : Type u) [metric_space α] [separable_space α] :
  ∃(f : α → ℓ_infty_ℝ), isometry f :=
begin
  cases (univ : set α).eq_empty_or_nonempty with h h,
  { use (λ_, 0), assume x, exact absurd h (nonempty.ne_empty ⟨x, mem_univ x⟩) },
  { /- We construct a map x : ℕ → α with dense image -/
    rcases h with ⟨basepoint⟩,
    haveI : inhabited α := ⟨basepoint⟩,
    have : ∃s:set α, countable s ∧ dense s := exists_countable_dense α,
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩,
    rcases countable_iff_exists_surjective.1 S_countable with ⟨x, x_range⟩,
    /- Use embedding_of_subset to construct the desired isometry -/
    exact ⟨embedding_of_subset x, embedding_of_subset_isometry x (S_dense.mono x_range)⟩ }
end
end Kuratowski_embedding

open topological_space Kuratowski_embedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/
def Kuratowski_embedding (α : Type u) [metric_space α] [separable_space α] : α → ℓ_infty_ℝ :=
  classical.some (Kuratowski_embedding.exists_isometric_embedding α)

/-- The Kuratowski embedding is an isometry. -/
protected lemma Kuratowski_embedding.isometry (α : Type u) [metric_space α] [separable_space α] :
  isometry (Kuratowski_embedding α) :=
classical.some_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
def nonempty_compacts.Kuratowski_embedding (α : Type u) [metric_space α] [compact_space α]
  [nonempty α] :
  nonempty_compacts ℓ_infty_ℝ :=
⟨range (Kuratowski_embedding α), range_nonempty _,
  is_compact_range (Kuratowski_embedding.isometry α).continuous⟩

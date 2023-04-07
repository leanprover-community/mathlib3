/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.metric_space.basic
import topology.algebra.order.archimedean
import topology.instances.int
import topology.instances.nat
import topology.instances.real
/-!
# Topology on the ratonal numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/
open metric set filter

namespace rat

-- without the `by exact` this is noncomputable
instance : metric_space ℚ :=
metric_space.induced coe (by exact rat.cast_injective) real.metric_space

theorem dist_eq (x y : ℚ) : dist x y = |x - y| := rfl

@[norm_cast, simp] lemma dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y := rfl

theorem uniform_continuous_coe_real : uniform_continuous (coe : ℚ → ℝ) :=
uniform_continuous_comap

theorem uniform_embedding_coe_real : uniform_embedding (coe : ℚ → ℝ) :=
uniform_embedding_comap rat.cast_injective

theorem dense_embedding_coe_real : dense_embedding (coe : ℚ → ℝ) :=
uniform_embedding_coe_real.dense_embedding rat.dense_range_cast

theorem embedding_coe_real : embedding (coe : ℚ → ℝ) := dense_embedding_coe_real.to_embedding

theorem continuous_coe_real : continuous (coe : ℚ → ℝ) := uniform_continuous_coe_real.continuous

end rat

@[norm_cast, simp] theorem nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y :=
by rw [← nat.dist_cast_real, ← rat.dist_cast]; congr' 1; norm_cast

lemma nat.uniform_embedding_coe_rat : uniform_embedding (coe : ℕ → ℚ) :=
uniform_embedding_bot_of_pairwise_le_dist zero_lt_one $ by simpa using nat.pairwise_one_le_dist

lemma nat.closed_embedding_coe_rat : closed_embedding (coe : ℕ → ℚ) :=
closed_embedding_of_pairwise_le_dist zero_lt_one $ by simpa using nat.pairwise_one_le_dist

@[norm_cast, simp] theorem int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y :=
by rw [← int.dist_cast_real, ← rat.dist_cast]; congr' 1; norm_cast

lemma int.uniform_embedding_coe_rat : uniform_embedding (coe : ℤ → ℚ) :=
uniform_embedding_bot_of_pairwise_le_dist zero_lt_one $ by simpa using int.pairwise_one_le_dist

lemma int.closed_embedding_coe_rat : closed_embedding (coe : ℤ → ℚ) :=
closed_embedding_of_pairwise_le_dist zero_lt_one $ by simpa using int.pairwise_one_le_dist

namespace rat

instance : noncompact_space ℚ := int.closed_embedding_coe_rat.noncompact_space

-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem uniform_continuous_add : uniform_continuous (λp : ℚ × ℚ, p.1 + p.2) :=
rat.uniform_embedding_coe_real.to_uniform_inducing.uniform_continuous_iff.2 $
  by simp only [(∘), rat.cast_add]; exact real.uniform_continuous_add.comp
    (rat.uniform_continuous_coe_real.prod_map rat.uniform_continuous_coe_real)

theorem uniform_continuous_neg : uniform_continuous (@has_neg.neg ℚ _) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [rat.dist_eq] using h⟩

instance : uniform_add_group ℚ :=
uniform_add_group.mk' rat.uniform_continuous_add rat.uniform_continuous_neg

instance : topological_add_group ℚ := by apply_instance

instance : order_topology ℚ :=
induced_order_topology _ (λ x y, rat.cast_lt) (@exists_rat_btwn _ _ _)

lemma uniform_continuous_abs : uniform_continuous (abs : ℚ → ℚ) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b h, lt_of_le_of_lt
    (by simpa [rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

lemma continuous_mul : continuous (λp : ℚ × ℚ, p.1 * p.2) :=
rat.embedding_coe_real.continuous_iff.2 $ by simp [(∘)]; exact
real.continuous_mul.comp ((rat.continuous_coe_real.prod_map rat.continuous_coe_real))

instance : topological_ring ℚ :=
{ continuous_mul := rat.continuous_mul, ..rat.topological_add_group }

lemma totally_bounded_Icc (a b : ℚ) : totally_bounded (Icc a b) :=
by simpa only [preimage_cast_Icc]
  using totally_bounded_preimage rat.uniform_embedding_coe_real (totally_bounded_Icc a b)

end rat

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.metric_space.basic
import order.filter.archimedean
/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/
noncomputable theory
open metric set filter

namespace int

instance : has_dist ℤ := ⟨λ x y, dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = |x - y| := rfl

@[norm_cast, simp] theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y := rfl

lemma pairwise_one_le_dist : pairwise (λ m n : ℤ, 1 ≤ dist m n) :=
begin
  intros m n hne,
  rw dist_eq, norm_cast, rwa [← zero_add (1 : ℤ), int.add_one_le_iff, abs_pos, sub_ne_zero]
end

lemma uniform_embedding_coe_real : uniform_embedding (coe : ℤ → ℝ) :=
uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

lemma closed_embedding_coe_real : closed_embedding (coe : ℤ → ℝ) :=
closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : metric_space ℤ := int.uniform_embedding_coe_real.comap_metric_space _

theorem preimage_ball (x : ℤ) (r : ℝ) : coe ⁻¹' (ball (x : ℝ) r) = ball x r := rfl

theorem preimage_closed_ball (x : ℤ) (r : ℝ) :
  coe ⁻¹' (closed_ball (x : ℝ) r) = closed_ball x r := rfl

theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ :=
by rw [← preimage_ball, real.ball_eq_Ioo, preimage_Ioo]

theorem closed_ball_eq_Icc (x : ℤ) (r : ℝ) : closed_ball x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ :=
by rw [← preimage_closed_ball, real.closed_ball_eq_Icc, preimage_Icc]

instance : proper_space ℤ :=
⟨ begin
    intros x r,
    rw closed_ball_eq_Icc,
    exact (set.finite_Icc _ _).is_compact,
  end ⟩

@[simp] lemma cocompact_eq : cocompact ℤ = at_bot ⊔ at_top :=
by simp only [← comap_dist_right_at_top_eq_cocompact (0 : ℤ), dist_eq, sub_zero, cast_zero,
  ← cast_abs, ← @comap_comap _ _ _ _ abs, int.comap_coe_at_top, comap_abs_at_top]

@[simp] lemma cofinite_eq : (cofinite : filter ℤ) = at_bot ⊔ at_top :=
by rw [← cocompact_eq_cofinite, cocompact_eq]

end int

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.instances.int
/-!
# Topology on the natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/
noncomputable theory
open metric set filter

namespace nat

noncomputable instance : has_dist ℕ := ⟨λ x y, dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = |x - y| := rfl

lemma dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y := rfl

@[norm_cast, simp] theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y := rfl

lemma pairwise_one_le_dist : pairwise (λ m n : ℕ, 1 ≤ dist m n) :=
begin
  intros m n hne,
  rw ← dist_coe_int,
  apply int.pairwise_one_le_dist,
  exact_mod_cast hne
end

lemma uniform_embedding_coe_real : uniform_embedding (coe : ℕ → ℝ) :=
uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

lemma closed_embedding_coe_real : closed_embedding (coe : ℕ → ℝ) :=
closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : metric_space ℕ := nat.uniform_embedding_coe_real.comap_metric_space _

theorem preimage_ball (x : ℕ) (r : ℝ) : coe ⁻¹' (ball (x : ℝ) r) = ball x r := rfl

theorem preimage_closed_ball (x : ℕ) (r : ℝ) :
  coe ⁻¹' (closed_ball (x : ℝ) r) = closed_ball x r := rfl

theorem closed_ball_eq_Icc (x : ℕ) (r : ℝ) :
  closed_ball x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ :=
begin
  rcases le_or_lt 0 r with hr|hr,
  { rw [← preimage_closed_ball, real.closed_ball_eq_Icc, preimage_Icc],
    exact add_nonneg (cast_nonneg x) hr },
  { rw closed_ball_eq_empty.2 hr,
    apply (Icc_eq_empty _).symm,
    rw not_le,
    calc ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ : by { apply floor_mono, linarith }
    ... < ⌈↑x - r⌉₊ : by { rw [floor_coe, nat.lt_ceil], linarith } }
end

instance : proper_space ℕ :=
⟨ begin
    intros x r,
    rw closed_ball_eq_Icc,
    exact (set.finite_Icc _ _).is_compact,
  end ⟩

instance : noncompact_space ℕ :=
noncompact_space_of_ne_bot $ by simp [filter.at_top_ne_bot]

end nat

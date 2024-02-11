/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import number_theory.liouville.basic
import topology.metric_space.baire
import topology.instances.irrational

/-!
# Density of Liouville numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/

open_locale filter
open filter set metric

lemma set_of_liouville_eq_Inter_Union :
  {x | liouville x} =
    ⋂ n : ℕ, ⋃ (a b : ℤ) (hb : 1 < b), ball (a / b) (1 / b ^ n) \ {a / b} :=
begin
  ext x,
  simp only [mem_Inter, mem_Union, liouville, mem_set_of_eq, exists_prop, mem_diff,
    mem_singleton_iff, mem_ball, real.dist_eq, and_comm]
end

lemma is_Gδ_set_of_liouville : is_Gδ {x | liouville x} :=
begin
  rw set_of_liouville_eq_Inter_Union,
  refine is_Gδ_Inter (λ n, is_open.is_Gδ _),
  refine is_open_Union (λ a, is_open_Union $ λ b, is_open_Union $ λ hb, _),
  exact is_open_ball.inter is_closed_singleton.is_open_compl
end

lemma set_of_liouville_eq_irrational_inter_Inter_Union :
  {x | liouville x} =
    {x | irrational x} ∩ ⋂ n : ℕ, ⋃ (a b : ℤ) (hb : 1 < b), ball (a / b) (1 / b ^ n) :=
begin
  refine subset.antisymm _ _,
  { refine subset_inter (λ x hx, hx.irrational) _,
    rw set_of_liouville_eq_Inter_Union,
    exact Inter_mono (λ n, Union₂_mono $ λ a b, Union_mono $ λ hb, diff_subset _ _) },
  { simp only [inter_Inter, inter_Union, set_of_liouville_eq_Inter_Union],
    refine Inter_mono (λ n, Union₂_mono $ λ a b, Union_mono $ λ hb, _),
    rw [inter_comm],
    refine diff_subset_diff subset.rfl (singleton_subset_iff.2 ⟨a / b, _⟩),
    norm_cast }
end

/-- The set of Liouville numbers is a residual set. -/
lemma eventually_residual_liouville : ∀ᶠ x in residual ℝ, liouville x :=
begin
  rw [filter.eventually, set_of_liouville_eq_irrational_inter_Inter_Union],
  refine eventually_residual_irrational.and _,
  refine eventually_residual.2 ⟨_, _, rat.dense_embedding_coe_real.dense.mono _, subset.rfl⟩,
  { exact is_Gδ_Inter (λ n, is_open.is_Gδ $ is_open_Union $ λ a, is_open_Union $
      λ b, is_open_Union $ λ hb, is_open_ball) },
  { rintro _ ⟨r, rfl⟩,
    simp only [mem_Inter, mem_Union],
    refine λ n, ⟨r.num * 2, r.denom * 2, _, _⟩,
    { have := int.coe_nat_le.2 r.pos, rw int.coe_nat_one at this, linarith },
    { convert mem_ball_self _ using 2,
      { push_cast, norm_cast, norm_num },
      { refine one_div_pos.2 (pow_pos (int.cast_pos.2 _) _),
        exact mul_pos (int.coe_nat_pos.2 r.pos) zero_lt_two } } }
end

/-- The set of Liouville numbers in dense. -/
lemma dense_liouville : dense {x | liouville x} :=
dense_of_mem_residual eventually_residual_liouville

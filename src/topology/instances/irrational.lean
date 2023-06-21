/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.real.irrational
import data.rat.encodable
import topology.metric_space.baire

/-!
# Topology of irrational numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove the following theorems:

* `is_Gδ_irrational`, `dense_irrational`, `eventually_residual_irrational`: irrational numbers
  form a dense Gδ set;

* `irrational.eventually_forall_le_dist_cast_div`,
  `irrational.eventually_forall_le_dist_cast_div_of_denom_le`;
  `irrational.eventually_forall_le_dist_cast_rat_of_denom_le`: a sufficiently small neighborhood of
  an irrational number is disjoint with the set of rational numbers with bounded denominator.

We also provide `order_topology`, `no_min_order`, `no_max_order`, and `densely_ordered`
instances for `{x // irrational x}`.

## Tags

irrational, residual
-/

open set filter metric
open_locale filter topology

lemma is_Gδ_irrational : is_Gδ {x | irrational x} :=
(countable_range _).is_Gδ_compl

lemma dense_irrational : dense {x : ℝ | irrational x} :=
begin
  refine real.is_topological_basis_Ioo_rat.dense_iff.2 _,
  simp only [mem_Union, mem_singleton_iff],
  rintro _ ⟨a, b, hlt, rfl⟩ hne, rw inter_comm,
  exact exists_irrational_btwn (rat.cast_lt.2 hlt)
end

lemma eventually_residual_irrational : ∀ᶠ x in residual ℝ, irrational x :=
eventually_residual.2 ⟨_, is_Gδ_irrational, dense_irrational, λ _, id⟩

namespace irrational

variable {x : ℝ}

instance : order_topology {x // irrational x} :=
induced_order_topology _ (λ x y, iff.rfl) $ λ x y hlt,
  let ⟨a, ha, hxa, hay⟩ := exists_irrational_btwn hlt in ⟨⟨a, ha⟩, hxa, hay⟩

instance : no_max_order {x // irrational x} :=
⟨λ ⟨x, hx⟩, ⟨⟨x + (1 : ℕ), hx.add_nat 1⟩, by simp⟩⟩

instance : no_min_order {x // irrational x} :=
⟨λ ⟨x, hx⟩, ⟨⟨x - (1 : ℕ), hx.sub_nat 1⟩, by simp⟩⟩

instance : densely_ordered {x // irrational x} :=
⟨λ x y hlt, let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt in ⟨⟨z, hz⟩, hxz, hzy⟩⟩

lemma eventually_forall_le_dist_cast_div (hx : irrational x) (n : ℕ) :
  ∀ᶠ ε : ℝ in 𝓝 0, ∀ m : ℤ, ε ≤ dist x (m / n) :=
begin
  have A : is_closed (range (λ m, n⁻¹ * m : ℤ → ℝ)),
    from ((is_closed_map_smul₀ (n⁻¹ : ℝ)).comp
      int.closed_embedding_coe_real.is_closed_map).closed_range,
  have B : x ∉ range (λ m, n⁻¹ * m : ℤ → ℝ),
  { rintro ⟨m, rfl⟩, simpa using hx },
  rcases metric.mem_nhds_iff.1 (A.is_open_compl.mem_nhds B) with ⟨ε, ε0, hε⟩,
  refine (ge_mem_nhds ε0).mono (λ δ hδ m, not_lt.1 $ λ hlt, _),
  rw dist_comm at hlt,
  refine hε (ball_subset_ball hδ hlt) ⟨m, _⟩,
  simp [div_eq_inv_mul]
end

lemma eventually_forall_le_dist_cast_div_of_denom_le (hx : irrational x) (n : ℕ) :
  ∀ᶠ ε : ℝ in 𝓝 0, ∀ (k ≤ n) (m : ℤ), ε ≤ dist x (m / k) :=
(finite_le_nat n).eventually_all.2 $ λ k hk, hx.eventually_forall_le_dist_cast_div k

lemma eventually_forall_le_dist_cast_rat_of_denom_le (hx : irrational x) (n : ℕ) :
  ∀ᶠ ε : ℝ in 𝓝 0, ∀ r : ℚ, r.denom ≤ n → ε ≤ dist x r :=
(hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono $ λ ε H r hr,
  by simpa only [rat.cast_def] using H r.denom hr r.num

end irrational

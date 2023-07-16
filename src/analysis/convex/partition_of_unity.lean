/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.partition_of_unity
import analysis.convex.combination

/-!
# Partition of unity and convex sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove the following lemma, see `exists_continuous_forall_mem_convex_of_local`. Let
`X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be a
topological real vector space. Let `t : X → set E` be a family of convex sets. Suppose that for each
point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is continuous
on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map `g : C(X, E)`
such that `g x ∈ t x` for all `x`.

We also formulate a useful corollary, see `exists_continuous_forall_mem_convex_of_local_const`, that
assumes that local functions `g` are constants.

## Tags

partition of unity
-/

open set function
open_locale big_operators topology

variables {ι X E : Type*} [topological_space X] [add_comm_group E] [module ℝ E]

lemma partition_of_unity.finsum_smul_mem_convex {s : set X} (f : partition_of_unity ι X s)
  {g : ι → X → E} {t : set E} {x : X} (hx : x ∈ s) (hg : ∀ i, f i x ≠ 0 → g i x ∈ t)
  (ht : convex ℝ t) :
  ∑ᶠ i, f i x • g i x ∈ t :=
ht.finsum_mem (λ i, f.nonneg _ _) (f.sum_eq_one hx) hg

variables [normal_space X] [paracompact_space X] [topological_space E] [has_continuous_add E]
  [has_continuous_smul ℝ E] {t : X → set E}

/-- Let `X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be
a topological real vector space. Let `t : X → set E` be a family of convex sets. Suppose that for
each point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is
continuous on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map
`g : C(X, E)` such that `g x ∈ t x` for all `x`. See also
`exists_continuous_forall_mem_convex_of_local_const`. -/
lemma exists_continuous_forall_mem_convex_of_local (ht : ∀ x, convex ℝ (t x))
  (H : ∀ x : X, ∃ (U ∈ 𝓝 x) (g : X → E), continuous_on g U ∧ ∀ y ∈ U, g y ∈ t y) : ∃
  g : C(X, E), ∀ x, g x ∈ t x :=
begin
  choose U hU g hgc hgt using H,
  obtain ⟨f, hf⟩ := partition_of_unity.exists_is_subordinate is_closed_univ (λ x, interior (U x))
    (λ x, is_open_interior) (λ x hx, mem_Union.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩),
  refine ⟨⟨λ x, ∑ᶠ i, f i x • g i x,
    hf.continuous_finsum_smul (λ i, is_open_interior) $ λ i, (hgc i).mono interior_subset⟩,
    λ x, f.finsum_smul_mem_convex (mem_univ x) (λ i hi, hgt _ _ _) (ht _)⟩,
  exact interior_subset (hf _ $ subset_closure hi)
end

/-- Let `X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be
a topological real vector space. Let `t : X → set E` be a family of convex sets. Suppose that for
each point `x : X`, there exists a vector `c : E` that belongs to `t y` for all `y` in a
neighborhood of `x`. Then there exists a continuous map `g : C(X, E)` such that `g x ∈ t x` for all
`x`. See also `exists_continuous_forall_mem_convex_of_local`. -/
lemma exists_continuous_forall_mem_convex_of_local_const (ht : ∀ x, convex ℝ (t x))
  (H : ∀ x : X, ∃ c : E, ∀ᶠ y in 𝓝 x, c ∈ t y) :
  ∃ g : C(X, E), ∀ x, g x ∈ t x :=
exists_continuous_forall_mem_convex_of_local ht $ λ x,
  let ⟨c, hc⟩ := H x in ⟨_, hc, λ _, c, continuous_on_const, λ y, id⟩

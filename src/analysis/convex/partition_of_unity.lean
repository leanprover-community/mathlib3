/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/

import topology.partition_of_unity
import analysis.convex.combination

/-!
-/

open set function
open_locale big_operators topological_space

variables {ι X E : Type*} [topological_space X] [add_comm_group E] [module ℝ E]

lemma partition_of_unity.finsum_smul_mem_convex {s : set X} (f : partition_of_unity ι X s)
  {g : ι → X → E} {t : set E} {x : X} (hx : x ∈ s) (hg : ∀ i, f i x ≠ 0 → g i x ∈ t)
  (ht : convex ℝ t) :
  ∑ᶠ i, f i x • g i x ∈ t :=
ht.finsum_mem (λ i, f.nonneg _ _) (f.sum_eq_one hx) hg

variables [normal_space X] [paracompact_space X] [topological_space E] [has_continuous_add E]
  [has_continuous_smul ℝ E]

lemma exists_continuous_forall_mem_convex_of_local {t : X → set E} (ht : ∀ x, convex ℝ (t x))
  (H : ∀ x : X, ∃ (U ∈ 𝓝 x) (g : X → E), continuous_on g U ∧ ∀ y ∈ U, g y ∈ t y) :
  ∃ g : C(X, E), ∀ x, g x ∈ t x :=
begin
  choose U hU g hgc hgt using H,
  obtain ⟨f, hf⟩ := partition_of_unity.exists_is_subordinate is_closed_univ (λ x, interior (U x))
    (λ x, is_open_interior) (λ x hx, mem_Union.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩),
  refine ⟨⟨λ x, ∑ᶠ i, f i x • g i x, f.continuous_finsum_smul $ λ i x hx, _⟩, λ x, _⟩,
  { exact (hgc _).continuous_at (mem_interior_iff_mem_nhds.1 $ hf _ hx) },
  { refine f.finsum_smul_mem_convex (mem_univ x) (λ i hi, hgt _ _ _) (ht _),
    exact interior_subset (hf _ $ subset_closure hi) }
end

/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.module.character_space
import analysis.normed_space.weak_dual
import analysis.normed_space.spectrum

/-!
# Normed algebras

This file contains basic facts about normed algebras.

## Main results

* We show that the character space of a normed algebra is compact using the Banach-Alaoglu theorem.

## TODO

* Show compactness for topological vector spaces; this requires the TVS version of Banach-Alaoglu.

## Tags

normed algebra, character space, continuous functional calculus

-/

variables {𝕜 : Type*} {A : Type*}

namespace weak_dual
namespace character_space

variables [nontrivially_normed_field 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] [complete_space A] [norm_one_class A]

lemma norm_one (φ : character_space 𝕜 A) : ∥to_normed_dual (φ : weak_dual 𝕜 A)∥ = 1 :=
begin
  refine continuous_linear_map.op_norm_eq_of_bounds zero_le_one (λ a, _) (λ x hx h, _),
  { rw [one_mul],
    exact spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ a) },
  { have : ∥φ 1∥ ≤ x * ∥(1 : A)∥ := h 1,
    simpa only [norm_one, mul_one, map_one] using this },
end

instance [proper_space 𝕜] : compact_space (character_space 𝕜 A) :=
begin
  rw [←is_compact_iff_compact_space],
  have h : character_space 𝕜 A ⊆ to_normed_dual ⁻¹' metric.closed_ball 0 1,
  { intros φ hφ,
    rw [set.mem_preimage, mem_closed_ball_zero_iff],
    exact (le_of_eq $ norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ : _), },
  exact compact_of_is_closed_subset (is_compact_closed_ball 𝕜 0 1) is_closed h,
end

end character_space
end weak_dual

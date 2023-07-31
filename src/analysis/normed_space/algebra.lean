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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  [normed_algebra 𝕜 A] [complete_space A]

lemma norm_le_norm_one (φ : character_space 𝕜 A) :
  ‖to_normed_dual (φ : weak_dual 𝕜 A)‖ ≤ ‖(1 : A)‖ :=
continuous_linear_map.op_norm_le_bound _ (norm_nonneg (1 : A)) $
  λ a, mul_comm (‖a‖) (‖(1 : A)‖) ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)

instance [proper_space 𝕜] : compact_space (character_space 𝕜 A) :=
begin
  rw [←is_compact_iff_compact_space],
  have h : character_space 𝕜 A ⊆ to_normed_dual ⁻¹' metric.closed_ball 0 (‖(1 : A)‖),
  { intros φ hφ,
    rw [set.mem_preimage, mem_closed_ball_zero_iff],
    exact (norm_le_norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ : _), },
  exact is_compact_of_is_closed_subset (is_compact_closed_ball 𝕜 0 _) character_space.is_closed h,
end

end character_space
end weak_dual

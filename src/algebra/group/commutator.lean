/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/

import algebra.group.defs
import data.bracket

/-!
# The bracket on a group given by commutator.
-/

/-- The commutator of two elements `g₁` and `g₂`. -/
instance commutator_element {G : Type*} [group G] : has_bracket G G :=
⟨λ g₁ g₂, g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

lemma commutator_element_def  {G : Type*} [group G] (g₁ g₂ : G) :
  ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := rfl

/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.module.weak_dual

/-!
# Gelfand space

Blah
-/

variables {𝕜 : Type*} {A : Type*}
  [comm_semiring 𝕜] [topological_space 𝕜]
  [semiring A] [topological_space A] [algebra 𝕜 A]

variables (𝕜) (A)

def gelfand_space : set (weak_dual 𝕜 A) :=
  {φ | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

def gelfand_space' :=
  {φ : A →L[𝕜] 𝕜 // (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

namespace gelfand_space

--example : fun_like (gelfand_space 𝕜 A) A (λ _, 𝕜) :=
--  continuous_linear_map.add_monoid_hom_class.to_zero_hom_class.to_fun_like

--example : fun_like (gelfand_space' 𝕜 A) A (λ _, 𝕜) := by apply_instance
example : fun_like (weak_dual 𝕜 A) A (λ _, 𝕜) := by apply_instance
example : zero_hom_class (weak_dual 𝕜 A) A 𝕜 := by apply_instance
example : add_monoid_hom_class (weak_dual 𝕜 A) A 𝕜 := by apply_instance
example : fun_like (A →L[𝕜] 𝕜) A (λ _, 𝕜) := by apply_instance

instance : ring_hom_class (gelfand_space 𝕜 A) A 𝕜 :=
{ coe := λ f, f.val.to_fun,
  coe_injective' := λ f g h, by { simp at h, refine subtype.coe_inj.mp h },
  map_one := sorry,
  map_mul := sorry,
  map_add := sorry,
  map_zero := sorry }

end gelfand_space

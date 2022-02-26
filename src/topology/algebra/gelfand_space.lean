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

def gelfand_space :=
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

namespace gelfand_space

instance : ring_hom_class (gelfand_space 𝕜 A) A 𝕜 :=
{ map_one := λ φ, φ.prop.1,
  map_mul := λ φ, φ.prop.2,
  ..subtype.add_monoid_hom_class (weak_dual 𝕜 A) A 𝕜 _ }

def to_alg_hom (φ : gelfand_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_one' := ring_hom_class.map_one _,
  map_mul' := ring_hom_class.map_mul _,
  map_zero' := ring_hom_class.map_zero _,
  map_add' := ring_hom_class.map_add _,
  commutes' := λ r, by
  { simp only [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id, ring_hom.id_apply],
    rw [@coe_fn_coe_base' _ (weak_dual 𝕜 A) _ _ _ φ],
    simp only [continuous_linear_map.map_smul, algebra.id.smul_eq_mul],
    change r * (φ 1) = r,
    simp only [map_one, mul_one] } }

end gelfand_space

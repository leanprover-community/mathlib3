/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.hom.group_action
import ring_theory.subring.pointwise

/-! # Subrings invariant under an action -/
section ring

variables (M R : Type*) [monoid M] [ring R] [mul_semiring_action M R]
variables (S : subring R)
open mul_action
variables {R}

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class is_invariant_subring : Prop :=
(smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S)

instance is_invariant_subring.to_mul_semiring_action [is_invariant_subring M S] :
  mul_semiring_action M S :=
{ smul := λ m x, ⟨m • x, is_invariant_subring.smul_mem m x.2⟩,
  one_smul := λ s, subtype.eq $ one_smul M s,
  mul_smul := λ m₁ m₂ s, subtype.eq $ mul_smul m₁ m₂ s,
  smul_add := λ m s₁ s₂, subtype.eq $ smul_add m s₁ s₂,
  smul_zero := λ m, subtype.eq $ smul_zero m,
  smul_one := λ m, subtype.eq $ smul_one m,
  smul_mul := λ m s₁ s₂, subtype.eq $ smul_mul' m s₁ s₂ }

end ring

section
variables (M : Type*) [monoid M]
variables {R' : Type*} [ring R'] [mul_semiring_action M R']
variables (U : subring R') [is_invariant_subring M U]

/-- The canonical inclusion from an invariant subring. -/
def is_invariant_subring.subtype_hom : U →+*[M] R' :=
{ map_smul' := λ m s, rfl, ..U.subtype }

@[simp] theorem is_invariant_subring.coe_subtype_hom :
  (is_invariant_subring.subtype_hom M U : U → R') = coe := rfl

@[simp] theorem is_invariant_subring.coe_subtype_hom' :
  (is_invariant_subring.subtype_hom M U : U →+* R') = U.subtype := rfl

end

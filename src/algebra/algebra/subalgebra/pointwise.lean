/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Weiser
-/
import algebra.algebra.operations
import algebra.algebra.subalgebra.basic
import ring_theory.subring.pointwise

namespace subalgebra

section pointwise
variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A] (S : subalgebra R A)

/-- As submodules, subalgebras are idempotent. -/
@[simp] theorem mul_self : S.to_submodule * S.to_submodule = S.to_submodule :=
begin
  apply le_antisymm,
  { rw submodule.mul_le,
    intros y hy z hz,
    exact mul_mem S hy hz },
  { intros x hx1,
    rw ← mul_one x,
    exact submodule.mul_mem_mul hx1 (one_mem S) }
end

variables {R' : Type*} [semiring R'] [mul_semiring_action R' A] [smul_comm_class R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action R' (subalgebra R A) :=
{ smul := λ a S, S.map (mul_semiring_action.to_alg_hom _ _ a),
  one_smul := λ S,
    (congr_arg (λ f, S.map f) (alg_hom.ext $ by exact one_smul R')).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (alg_hom.ext $ by exact mul_smul _ _)).trans (S.map_map _ _).symm }

localized "attribute [instance] subalgebra.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (m : R') (S : subalgebra R A) : ↑(m • S) = m • (S : set A) := rfl

@[simp] lemma pointwise_smul_to_subsemiring (m : R') (S : subalgebra R A) :
  (m • S).to_subsemiring = m • S.to_subsemiring := rfl

@[simp] lemma pointwise_smul_to_submodule (m : R') (S : subalgebra R A) :
  (m • S).to_submodule = m • S.to_submodule := rfl

@[simp] lemma pointwise_smul_to_subring {R' R A : Type*} [semiring R'] [comm_ring R] [ring A]
  [mul_semiring_action R' A] [algebra R A] [smul_comm_class R' R A] (m : R') (S : subalgebra R A) :
  (m • S).to_subring = m • S.to_subring := rfl

lemma smul_mem_pointwise_smul (m : R') (r : A) (S : subalgebra R A) : r ∈ S → m • r ∈ m • S :=
(set.smul_mem_smul_set : _ → _ ∈ m • (S : set A))

end pointwise

end subalgebra

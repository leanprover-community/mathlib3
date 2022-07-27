/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.operations
import algebra.algebra.subalgebra.basic
import ring_theory.subring.pointwise
import ring_theory.adjoin.basic

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/

namespace subalgebra

section pointwise
variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

theorem mul_to_submodule_le (S T : subalgebra R A) :
  S.to_submodule * T.to_submodule ≤ (S ⊔ T).to_submodule :=
begin
  rw submodule.mul_le,
  intros y hy z hz,
  show y * z ∈ (S ⊔ T),
  exact mul_mem (algebra.mem_sup_left hy) (algebra.mem_sup_right hz),
end

/-- As submodules, subalgebras are idempotent. -/
@[simp] theorem mul_self  (S : subalgebra R A) : S.to_submodule * S.to_submodule = S.to_submodule :=
begin
  apply le_antisymm,
  { refine (mul_to_submodule_le _ _).trans_eq _,
    rw sup_idem },
  { intros x hx1,
    rw ← mul_one x,
    exact submodule.mul_mem_mul hx1 (show (1 : A) ∈ S, from one_mem S) }
end

/-- When `A` is commutative, `subalgebra.mul_to_submodule_le` is strict. -/
theorem mul_to_submodule {R : Type*} {A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]
  (S T : subalgebra R A) :
  S.to_submodule * T.to_submodule = (S ⊔ T).to_submodule :=
begin
  refine le_antisymm (mul_to_submodule_le _ _) _,
  rintros x (hx : x ∈ algebra.adjoin R (S ∪ T : set A)),
  refine algebra.adjoin_induction hx (λ x hx, _) (λ r, _) (λ _ _, submodule.add_mem _)
    (λ x y hx hy, _),
  { cases hx with hxS hxT,
    { rw ← mul_one x,
      exact submodule.mul_mem_mul hxS (show (1 : A) ∈ T, from one_mem T) },
    { rw ← one_mul x,
      exact submodule.mul_mem_mul (show (1 : A) ∈ S, from one_mem S) hxT } },
  { rw ← one_mul (algebra_map _ _ _),
    exact submodule.mul_mem_mul (show (1 : A) ∈ S, from one_mem S) (algebra_map_mem _ _) },
  have := submodule.mul_mem_mul hx hy,
  rwa [mul_assoc, mul_comm _ T.to_submodule, ←mul_assoc _ _ S.to_submodule, mul_self,
    mul_comm T.to_submodule, ←mul_assoc, mul_self] at this,
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

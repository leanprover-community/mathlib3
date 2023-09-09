/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.restrict_scalars
import algebra.lie.tensor_product

/-!
# Extension and restriction of scalars for Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lie algebras have a well-behaved theory of extension and restriction of scalars.

## Main definitions

 * `lie_algebra.extend_scalars.lie_algebra`
 * `lie_algebra.restrict_scalars.lie_algebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/

universes u v w w₁ w₂ w₃

open_locale tensor_product

variables (R : Type u) (A : Type w) (L : Type v)

namespace lie_algebra

namespace extend_scalars

variables [comm_ring R] [comm_ring A] [algebra R A] [lie_ring L] [lie_algebra R L]

/-- The Lie bracket on the extension of a Lie algebra `L` over `R` by an algebra `A` over `R`.

In fact this bracket is fully `A`-bilinear but without a significant upgrade to our mixed-scalar
support in the tensor product library, it is far easier to bootstrap like this, starting with the
definition below. -/
private def bracket' : (A ⊗[R] L) →ₗ[R] (A ⊗[R] L) →ₗ[R] A ⊗[R] L :=
tensor_product.curry $
  (tensor_product.map (linear_map.mul' R _) (lie_module.to_module_hom R L L : L ⊗[R] L →ₗ[R] L))
  ∘ₗ ↑(tensor_product.tensor_tensor_tensor_comm R A L A L)

@[simp] private lemma bracket'_tmul (s t : A) (x y : L) :
  bracket' R A L (s ⊗ₜ[R] x) (t ⊗ₜ[R] y) = (s*t) ⊗ₜ ⁅x, y⁆ :=
by simp [bracket']

instance : has_bracket (A ⊗[R] L) (A ⊗[R] L) := { bracket := λ x y, bracket' R A L x y, }

private lemma bracket_def (x y : A ⊗[R] L) : ⁅x, y⁆ = bracket' R A L x y := rfl

@[simp] lemma bracket_tmul (s t : A) (x y : L) : ⁅s ⊗ₜ[R] x, t ⊗ₜ[R] y⁆ = (s*t) ⊗ₜ ⁅x, y⁆ :=
by rw [bracket_def, bracket'_tmul]

private lemma bracket_lie_self (x : A ⊗[R] L) : ⁅x, x⁆ = 0 :=
begin
  simp only [bracket_def],
  apply x.induction_on,
  { simp only [linear_map.map_zero, eq_self_iff_true, linear_map.zero_apply], },
  { intros a l,
    simp only [bracket'_tmul, tensor_product.tmul_zero, eq_self_iff_true, lie_self], },
  { intros z₁ z₂ h₁ h₂,
    suffices : bracket' R A L z₁ z₂ + bracket' R A L z₂ z₁ = 0,
    { rw [linear_map.map_add, linear_map.map_add, linear_map.add_apply, linear_map.add_apply,
        h₁, h₂, zero_add, add_zero, add_comm, this], },
    apply z₁.induction_on,
    { simp only [linear_map.map_zero, add_zero, linear_map.zero_apply], },
    { intros a₁ l₁, apply z₂.induction_on,
      { simp only [linear_map.map_zero, add_zero, linear_map.zero_apply], },
      { intros a₂ l₂,
        simp only [← lie_skew l₂ l₁, mul_comm a₁ a₂, tensor_product.tmul_neg, bracket'_tmul,
          add_right_neg], },
      { intros y₁ y₂ hy₁ hy₂,
        simp only [hy₁, hy₂, add_add_add_comm, add_zero, linear_map.add_apply,
          linear_map.map_add], }, },
    { intros y₁ y₂ hy₁ hy₂,
      simp only [add_add_add_comm, hy₁, hy₂, add_zero, linear_map.add_apply,
        linear_map.map_add], }, },
end

private lemma bracket_leibniz_lie (x y z : A ⊗[R] L) : ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ :=
begin
  simp only [bracket_def],
  apply x.induction_on,
  { simp only [linear_map.map_zero, add_zero, eq_self_iff_true, linear_map.zero_apply], },
  { intros a₁ l₁,
    apply y.induction_on,
    { simp only [linear_map.map_zero, add_zero, eq_self_iff_true, linear_map.zero_apply], },
    { intros a₂ l₂,
      apply z.induction_on,
      { simp only [linear_map.map_zero, add_zero], },
      { intros a₃ l₃, simp only [bracket'_tmul],
        rw [mul_left_comm a₂ a₁ a₃, mul_assoc, leibniz_lie, tensor_product.tmul_add], },
      { intros u₁ u₂ h₁ h₂,
        simp only [add_add_add_comm, h₁, h₂, linear_map.map_add], }, },
    { intros u₁ u₂ h₁ h₂,
      simp only [add_add_add_comm, h₁, h₂, linear_map.add_apply, linear_map.map_add], }, },
  { intros u₁ u₂ h₁ h₂,
    simp only [add_add_add_comm, h₁, h₂, linear_map.add_apply, linear_map.map_add], },
end

instance : lie_ring (A ⊗[R] L) :=
{ add_lie     := λ x y z, by simp only [bracket_def, linear_map.add_apply, linear_map.map_add],
  lie_add     := λ x y z, by simp only [bracket_def, linear_map.map_add],
  lie_self    := bracket_lie_self R A L,
  leibniz_lie := bracket_leibniz_lie R A L, }

private lemma bracket_lie_smul (a : A) (x y : A ⊗[R] L) : ⁅x, a • y⁆ = a • ⁅x, y⁆ :=
begin
  apply x.induction_on,
  { simp only [zero_lie, smul_zero], },
  { intros a₁ l₁, apply y.induction_on,
    { simp only [lie_zero, smul_zero], },
    { intros a₂ l₂,
      simp only [bracket_def, bracket', tensor_product.smul_tmul', mul_left_comm a₁ a a₂,
        tensor_product.curry_apply, linear_map.mul'_apply, algebra.id.smul_eq_mul,
        function.comp_app, linear_equiv.coe_coe, linear_map.coe_comp, tensor_product.map_tmul,
        tensor_product.tensor_tensor_tensor_comm_tmul], },
    { intros z₁ z₂ h₁ h₂,
      simp only [h₁, h₂, smul_add, lie_add], }, },
  { intros z₁ z₂ h₁ h₂,
    simp only [h₁, h₂, smul_add, add_lie], },
end

instance lie_algebra : lie_algebra A (A ⊗[R] L) :=
{ lie_smul := bracket_lie_smul R A L, }

end extend_scalars

namespace restrict_scalars

open restrict_scalars

variables [h : lie_ring L]

include h

instance : lie_ring (restrict_scalars R A L) := h

variables [comm_ring A] [lie_algebra A L]

instance lie_algebra [comm_ring R] [algebra R A] : lie_algebra R (restrict_scalars R A L) :=
{ lie_smul := λ t x y, (lie_smul (algebra_map R A t)
    (restrict_scalars.add_equiv R A L x) (restrict_scalars.add_equiv R A L y) : _) }

end restrict_scalars

end lie_algebra

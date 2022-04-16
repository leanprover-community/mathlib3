/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.hom.group_instances
import algebra.ring.opposite
import group_theory.group_action.opposite
import group_theory.group_action.prod

/-!
# Scalar actions preserving zero

This file defines a few types of scalar actions with left and right absorbent zeroes.

## Main declarations

* `smul_with_zero`: Scalar action such that `r • 0 = 0` and `0 • m = 0` for all `r` and `m`.
* `mul_action_with_zero`: Combination of `mul_action` and `smul_with_zero`.
* `distrib_mul_action_with_zero`: Combination of `distrib_mul_action` and `smul_with_zero`.

* `smul_monoid_with_zero_hom`: Scalar multiplication bundled as a morphism of monoids with zero.
-/

open function

variables {R R' M M' : Type*}

section has_zero

variables (R M)
/--  `smul_with_zero` is a class consisting of a Type `R` with `0 ∈ R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class smul_with_zero [has_zero R] [has_zero M] extends has_scalar R M :=
(smul_zero : ∀ r : R, r • (0 : M) = 0)
(zero_smul : ∀ m : M, (0 : R) • m = 0)

instance mul_zero_class.to_smul_with_zero [mul_zero_class R] : smul_with_zero R R :=
{ smul := (*),
  smul_zero := mul_zero,
  zero_smul := zero_mul }

/-- Like `mul_zero_class.to_smul_with_zero`, but multiplies on the right. -/
instance mul_zero_class.to_opposite_smul_with_zero [mul_zero_class R] : smul_with_zero Rᵐᵒᵖ R :=
{ smul := (•),
  smul_zero := λ r, zero_mul _,
  zero_smul := mul_zero }

variables (R) {M} [has_zero R] [has_zero M] [smul_with_zero R M]

@[simp] lemma zero_smul (m : M) : (0 : R) • m = 0 := smul_with_zero.zero_smul m

variables {R} (M)
/-- Note that this lemma has different typeclass assumptions to `smul_zero`. -/
@[simp] lemma smul_zero' (r : R) : r • (0 : M) = 0 := smul_with_zero.smul_zero r

variables {R M} [has_zero R'] [has_zero M'] [has_scalar R M']

/-- Pullback a `smul_with_zero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.smul_with_zero
  (f : zero_hom M' M) (hf : function.injective f) (smul : ∀ (a : R) b, f (a • b) = a • f b) :
  smul_with_zero R M' :=
{ smul := (•),
  zero_smul := λ a, hf $ by simp [smul],
  smul_zero := λ a, hf $ by simp [smul]}

/-- Pushforward a `smul_with_zero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.smul_with_zero
  (f : zero_hom M M') (hf : function.surjective f) (smul : ∀ (a : R) b, f (a • b) = a • f b) :
  smul_with_zero R M' :=
{ smul := (•),
  zero_smul := λ m, by { rcases hf m with ⟨x, rfl⟩, simp [←smul] },
  smul_zero := λ c, by simp only [← f.map_zero, ← smul, smul_zero'] }

variables (M)

/-- Compose a `smul_with_zero` with a `zero_hom`, with action `f r' • m` -/
def smul_with_zero.comp_hom (f : zero_hom R' R) : smul_with_zero R' M :=
{ smul := (•) ∘ f,
  smul_zero := λ m, by simp,
  zero_smul := λ m, by simp }

end has_zero

instance add_monoid.nat_smul_with_zero [add_monoid M] : smul_with_zero ℕ M :=
{ smul_zero := nsmul_zero,
  zero_smul := zero_nsmul }

instance add_group.int_smul_with_zero [add_group M] : smul_with_zero ℤ M :=
{ smul_zero := zsmul_zero,
  zero_smul := zero_zsmul }

section monoid_with_zero
variables [monoid_with_zero R] [monoid_with_zero R']

section has_zero
variables [has_zero M] (R M)

/--  An action of a monoid with zero `R` on a Type `M`, also with `0`, extends `mul_action` and
is compatible with `0` (both in `R` and in `M`), with `1 ∈ R`, and with associativity of
multiplication on the monoid `M`. -/
class mul_action_with_zero extends mul_action R M :=
-- these fields are copied from `smul_with_zero`, as `extends` behaves poorly
(smul_zero : ∀ r : R, r • (0 : M) = 0)
(zero_smul : ∀ m : M, (0 : R) • m = 0)

@[priority 100] -- see Note [lower instance priority]
instance mul_action_with_zero.to_smul_with_zero [m : mul_action_with_zero R M] :
  smul_with_zero R M :=
{..m}

/-- See also `semiring.to_module` -/
instance monoid_with_zero.to_mul_action_with_zero : mul_action_with_zero R R :=
{ ..mul_zero_class.to_smul_with_zero R,
  ..monoid.to_mul_action R }

/-- Like `monoid_with_zero.to_mul_action_with_zero`, but multiplies on the right. See also
`semiring.to_opposite_module` -/
instance monoid_with_zero.to_opposite_mul_action_with_zero : mul_action_with_zero Rᵐᵒᵖ R :=
{ ..mul_zero_class.to_opposite_smul_with_zero R,
  ..monoid.to_opposite_mul_action R }

variables {R M} [mul_action_with_zero R M] [has_zero M'] [has_scalar R M']

/-- Pullback a `mul_action_with_zero` structure along an injective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.mul_action_with_zero
  (f : zero_hom M' M) (hf : function.injective f) (smul : ∀ (a : R) b, f (a • b) = a • f b) :
  mul_action_with_zero R M' :=
{ ..hf.mul_action f smul, ..hf.smul_with_zero f smul }

/-- Pushforward a `mul_action_with_zero` structure along a surjective zero-preserving homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.mul_action_with_zero
  (f : zero_hom M M') (hf : function.surjective f) (smul : ∀ (a : R) b, f (a • b) = a • f b) :
  mul_action_with_zero R M' :=
{ ..hf.mul_action f smul, ..hf.smul_with_zero f smul }

variables (M)

/-- Compose a `mul_action_with_zero` with a `monoid_with_zero_hom`, with action `f r' • m` -/
def mul_action_with_zero.comp_hom (f : R' →*₀ R) : mul_action_with_zero R' M :=
{ smul := (•) ∘ f,
  mul_smul := λ r s m, by simp [mul_smul],
  one_smul := λ m, by simp,
  .. smul_with_zero.comp_hom M f.to_zero_hom}

end has_zero

section add_monoid
variables [add_monoid M] (R M)

/-- Typeclass for a distributive multiplicative action of a monoid with zero `R` on an additive
monoid `M` such that `0 : R` is left-absorbent and `0 : M` is right-absorbent. -/
@[ext] class distrib_mul_action_with_zero extends distrib_mul_action R M :=
-- this field is copied from `mul_action_with_zero`, as `extends` behaves poorly
(zero_smul : ∀ m : M, (0 : R) • m = 0)

@[priority 100] -- see Note [lower instance priority]
instance distrib_mul_action_with_zero.to_mul_action_with_zero
  [m : distrib_mul_action_with_zero R M] :
  mul_action_with_zero R M :=
{..m}

variables {R M} [distrib_mul_action_with_zero R M] [add_monoid M'] [has_scalar R M']

/-- Pullback a `distrib_mul_action_with_zero` structure along an injective monoid homomorphism. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.distrib_mul_action_with_zero (f : M' →+ M) (hf : injective f)
  (smul : ∀ (a : R) b, f (a • b) = a • f b) :
  distrib_mul_action_with_zero R M' :=
{ ..hf.distrib_mul_action f smul, ..hf.mul_action_with_zero (f : zero_hom M' M) smul }

/-- Pushforward a `distrib_mul_action_with_zero` structure along a surjective monoid homomorphism.
-/
@[reducible] -- See note [reducible non-instances]
protected def function.surjective.distrib_mul_action_with_zero (f : M →+ M') (hf : surjective f)
  (smul : ∀ (a : R) b, f (a • b) = a • f b) :
  distrib_mul_action_with_zero R M' :=
{ ..hf.distrib_mul_action f smul, ..hf.mul_action_with_zero (f : zero_hom M M') smul }

variables (M)

/-- Compose a `distrib_mul_action_with_zero` with a `monoid_with_zero_hom`, with action
`f r' • m`. -/
def distrib_mul_action_with_zero.comp_hom (f : R' →*₀ R) : distrib_mul_action_with_zero R' M :=
{ ..distrib_mul_action.comp_hom M f.to_monoid_hom, ..mul_action_with_zero.comp_hom M f }

variables (R)

/-- (•) as a monoid with zero homomorphism. For each element `a` of the monoid, `λ b, a • b` is an
additive monoid endomorphism.

This is a stronger version of `distrib_mul_action.to_add_monoid_End`. -/
@[simps] def distrib_mul_action_with_zero.to_add_monoid_End : R →*₀ add_monoid.End M :=
{ map_zero' := add_monoid_hom.ext $ λ x, zero_smul _ _,
  ..distrib_mul_action.to_add_monoid_End R M }

end add_monoid
end monoid_with_zero

section group_with_zero
variables {α β : Type*} [group_with_zero α] [group_with_zero β] [mul_action_with_zero α β]

lemma smul_inv₀ [smul_comm_class α β β] [is_scalar_tower α β β] (c : α) (x : β) :
  (c • x)⁻¹ = c⁻¹ • x⁻¹ :=
begin
  obtain rfl | hc := eq_or_ne c 0,
  { simp only [inv_zero, zero_smul] },
  obtain rfl | hx := eq_or_ne x 0,
  { simp only [inv_zero, smul_zero'] },
  { refine (eq_inv_of_mul_left_eq_one _).symm,
    rw [smul_mul_smul, inv_mul_cancel hc, inv_mul_cancel hx, one_smul] }
end

end group_with_zero

/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
def smul_monoid_with_zero_hom {α β : Type*} [monoid_with_zero α] [mul_zero_one_class β]
  [mul_action_with_zero α β] [is_scalar_tower α β β] [smul_comm_class α β β] :
  α × β →*₀ β :=
{ map_zero' := smul_zero' _ _,
  .. smul_monoid_hom }

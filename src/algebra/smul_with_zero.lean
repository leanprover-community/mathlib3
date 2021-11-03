/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group_power.basic
import algebra.opposites

/-!
# Introduce `smul_with_zero`

In analogy with the usual monoid action on a Type `M`, we introduce an action of a
`monoid_with_zero` on a Type with `0`.

In particular, for Types `R` and `M`, both containing `0`, we define `smul_with_zero R M` to
be the typeclass where the products `r • 0` and `0 • m` vanish for all `r : R` and all `m : M`.

Moreover, in the case in which `R` is a `monoid_with_zero`, we introduce the typeclass
`mul_action_with_zero R M`, mimicking group actions and having an absorbing `0` in `R`.
Thus, the action is required to be compatible with

* the unit of the monoid, acting as the identity;
* the zero of the monoid_with_zero, acting as zero;
* associativity of the monoid.

We also add an `instance`:

* any `monoid_with_zero` has a `mul_action_with_zero R R` acting on itself.
-/

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
instance mul_zero_class.to_opposite_smul_with_zero [mul_zero_class R] : smul_with_zero Rᵒᵖ R :=
{ smul := (•),
  smul_zero := λ r, zero_mul _,
  zero_smul := mul_zero }

instance add_monoid.to_smul_with_zero [add_monoid M] : smul_with_zero ℕ M :=
{ smul_zero := nsmul_zero,
  zero_smul := zero_nsmul }

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

section monoid_with_zero

variables [monoid_with_zero R] [monoid_with_zero R'] [has_zero M]

variables (R M)
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
instance monoid_with_zero.to_opposite_mul_action_with_zero : mul_action_with_zero Rᵒᵖ R :=
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
def mul_action_with_zero.comp_hom (f : monoid_with_zero_hom R' R) :
  mul_action_with_zero R' M :=
{ smul := (•) ∘ f,
  mul_smul := λ r s m, by simp [mul_smul],
  one_smul := λ m, by simp,
  .. smul_with_zero.comp_hom M f.to_zero_hom}

end monoid_with_zero

/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.basic
import algebra.hom.iterate
import algebra.hom.non_unital_alg
import linear_algebra.tensor_product

/-!
# Facts about algebras involving bilinear maps and tensor products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We move a few basic statements about algebras out of `algebra.algebra.basic`,
in order to avoid importing `linear_algebra.bilinear_map` and
`linear_algebra.tensor_product` unnecessarily.
-/

open_locale tensor_product
open module

namespace linear_map

section non_unital_non_assoc

variables (R A : Type*) [comm_semiring R] [non_unital_non_assoc_semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `add_monoid_hom.mul`. -/
def mul : A →ₗ[R] A →ₗ[R] A := linear_map.mk₂ R (*) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def mul' : A ⊗[R] A →ₗ[R] A :=
tensor_product.lift (mul R A)

variables {A}

/-- The multiplication on the left in a non-unital algebra is a linear map. -/
def mul_left (a : A) : A →ₗ[R] A := mul R A a

/-- The multiplication on the right in an algebra is a linear map. -/
def mul_right (a : A) : A →ₗ[R] A := (mul R A).flip a

/-- Simultaneous multiplication on the left and right is a linear map. -/
def mul_left_right (ab : A × A) : A →ₗ[R] A := (mul_right R ab.snd).comp (mul_left R ab.fst)

@[simp] lemma mul_left_to_add_monoid_hom (a : A) :
  (mul_left R a : A →+ A) = add_monoid_hom.mul_left a := rfl

@[simp] lemma mul_right_to_add_monoid_hom (a : A) :
  (mul_right R a : A →+ A) = add_monoid_hom.mul_right a := rfl

variables {R}

@[simp] lemma mul_apply' (a b : A) : mul R A a b = a * b := rfl
@[simp] lemma mul_left_apply (a b : A) : mul_left R a b = a * b := rfl
@[simp] lemma mul_right_apply (a b : A) : mul_right R a b = b * a := rfl
@[simp] lemma mul_left_right_apply (a b x : A) : mul_left_right R (a, b) x = a * x * b := rfl

@[simp] lemma mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b := rfl

@[simp] lemma mul_left_zero_eq_zero :
  mul_left R (0 : A) = 0 :=
(mul R A).map_zero

@[simp] lemma mul_right_zero_eq_zero :
  mul_right R (0 : A) = 0 :=
(mul R A).flip.map_zero

end non_unital_non_assoc

section non_unital

variables (R A : Type*) [comm_semiring R] [non_unital_semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]

/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `linear_map.mul`. -/
def _root_.non_unital_alg_hom.lmul : A →ₙₐ[R] (End R A) :=
{ map_mul' := by { intros a b, ext c, exact mul_assoc a b c },
  map_zero' := by { ext a, exact zero_mul a },
  .. (mul R A) }

variables {R A}

@[simp]
lemma _root_.non_unital_alg_hom.coe_lmul_eq_mul : ⇑(non_unital_alg_hom.lmul R A) = mul R A := rfl

lemma commute_mul_left_right (a b : A) :
  commute (mul_left R a) (mul_right R b) :=
by { ext c, exact (mul_assoc a c b).symm, }

@[simp] lemma mul_left_mul (a b : A) :
  mul_left R (a * b) = (mul_left R a).comp (mul_left R b) :=
by { ext, simp only [mul_left_apply, comp_apply, mul_assoc] }

@[simp] lemma mul_right_mul (a b : A) :
  mul_right R (a * b) = (mul_right R b).comp (mul_right R a) :=
by { ext, simp only [mul_right_apply, comp_apply, mul_assoc] }

end non_unital

section semiring

variables (R A : Type*) [comm_semiring R] [semiring A] [algebra R A]

/-- The multiplication in an algebra is an algebra homomorphism into the endomorphisms on
the algebra.

A weaker version of this for non-unital algebras exists as `non_unital_alg_hom.mul`. -/
def _root_.algebra.lmul : A →ₐ[R] (End R A) :=
{ map_one' := by { ext a, exact one_mul a },
  map_mul' := by { intros a b, ext c, exact mul_assoc a b c },
  map_zero' := by { ext a, exact zero_mul a },
  commutes' := by { intro r, ext a, exact (algebra.smul_def r a).symm, },
  .. (linear_map.mul R A) }

variables {R A}

@[simp] lemma _root_.algebra.coe_lmul_eq_mul : ⇑(algebra.lmul R A) = mul R A := rfl

@[simp] lemma mul_left_eq_zero_iff (a : A) :
  mul_left R a = 0 ↔ a = 0 :=
begin
  split; intros h,
  { rw [← mul_one a, ← mul_left_apply a 1, h, linear_map.zero_apply], },
  { rw h, exact mul_left_zero_eq_zero, },
end

@[simp] lemma mul_right_eq_zero_iff (a : A) :
  mul_right R a = 0 ↔ a = 0 :=
begin
  split; intros h,
  { rw [← one_mul a, ← mul_right_apply a 1, h, linear_map.zero_apply], },
  { rw h, exact mul_right_zero_eq_zero, },
end

@[simp] lemma mul_left_one : mul_left R (1:A) = linear_map.id :=
by { ext, simp only [linear_map.id_coe, one_mul, id.def, mul_left_apply] }

@[simp] lemma mul_right_one : mul_right R (1:A) = linear_map.id :=
by { ext, simp only [linear_map.id_coe, mul_one, id.def, mul_right_apply] }

@[simp] lemma pow_mul_left (a : A) (n : ℕ) :
  (mul_left R a) ^ n = mul_left R (a ^ n) :=
by simpa only [mul_left, ←algebra.coe_lmul_eq_mul] using ((algebra.lmul R A).map_pow a n).symm

@[simp] lemma pow_mul_right (a : A) (n : ℕ) :
  (mul_right R a) ^ n = mul_right R (a ^ n) :=
begin
  simp only [mul_right, ←algebra.coe_lmul_eq_mul],
  exact linear_map.coe_injective
    (((mul_right R a).coe_pow n).symm ▸ (mul_right_iterate a n)),
end

end semiring

section ring

variables {R A : Type*} [comm_semiring R] [ring A] [algebra R A]

lemma mul_left_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (mul_left R x) :=
begin
  letI : nontrivial A := ⟨⟨x, 0, hx⟩⟩,
  letI := no_zero_divisors.to_is_domain A,
  exact mul_right_injective₀ hx,
end

lemma mul_right_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (mul_right R x) :=
begin
  letI : nontrivial A := ⟨⟨x, 0, hx⟩⟩,
  letI := no_zero_divisors.to_is_domain A,
  exact mul_left_injective₀ hx,
end

lemma mul_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (mul R A x) :=
begin
  letI : nontrivial A := ⟨⟨x, 0, hx⟩⟩,
  letI := no_zero_divisors.to_is_domain A,
  exact mul_right_injective₀ hx,
end

end ring

end linear_map

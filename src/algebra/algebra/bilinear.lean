/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.basic
import linear_algebra.tensor_product

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `algebra.algebra.basic`,
in order to avoid importing `linear_algebra.bilinear_map` and
`linear_algebra.tensor_product` unnecessarily.
-/

universes u v w

namespace algebra

open_locale tensor_product
open module

section

variables (R A : Type*) [comm_semiring R] [semiring A] [algebra R A]

/-- The multiplication in an algebra is a bilinear map.

A weaker version of this for semirings exists as `add_monoid_hom.mul`. -/
def lmul : A →ₐ[R] (End R A) :=
{ map_one' := by { ext a, exact one_mul a },
  map_mul' := by { intros a b, ext c, exact mul_assoc a b c },
  map_zero' := by { ext a, exact zero_mul a },
  commutes' := by { intro r, ext a, dsimp, rw [smul_def] },
  .. (show A →ₗ[R] A →ₗ[R] A, from linear_map.mk₂ R (*)
  (λ x y z, add_mul x y z)
  (λ c x y, by rw [smul_def, smul_def, mul_assoc _ x y])
  (λ x y z, mul_add x y z)
  (λ c x y, by rw [smul_def, smul_def, left_comm])) }

variables {R A}

@[simp] lemma lmul_apply (p q : A) : lmul R A p q = p * q := rfl


variables (R)

/-- The multiplication on the left in an algebra is a linear map. -/
def lmul_left (r : A) : A →ₗ[R] A :=
lmul R A r

/-- The multiplication on the right in an algebra is a linear map. -/
def lmul_right (r : A) : A →ₗ[R] A :=
(lmul R A).to_linear_map.flip r

/-- Simultaneous multiplication on the left and right is a linear map. -/
def lmul_left_right (vw: A × A) : A →ₗ[R] A :=
(lmul_right R vw.2).comp (lmul_left R vw.1)

lemma commute_lmul_left_right (a b : A) :
  commute (lmul_left R a) (lmul_right R b) :=
by { ext c, exact (mul_assoc a c b).symm, }

/-- The multiplication map on an algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def lmul' : A ⊗[R] A →ₗ[R] A :=
tensor_product.lift (lmul R A).to_linear_map

variables {R A}

@[simp] lemma lmul'_apply {x y : A} : lmul' R (x ⊗ₜ y) = x * y :=
by simp only [algebra.lmul', tensor_product.lift.tmul, alg_hom.to_linear_map_apply, lmul_apply]

@[simp] lemma lmul_left_apply (p q : A) : lmul_left R p q = p * q := rfl
@[simp] lemma lmul_right_apply (p q : A) : lmul_right R p q = q * p := rfl
@[simp] lemma lmul_left_right_apply (vw : A × A) (p : A) :
  lmul_left_right R vw p = vw.1 * p * vw.2 := rfl

@[simp] lemma lmul_left_one : lmul_left R (1:A) = linear_map.id :=
by { ext, simp only [linear_map.id_coe, one_mul, id.def, lmul_left_apply] }

@[simp] lemma lmul_left_mul (a b : A) :
  lmul_left R (a * b) = (lmul_left R a).comp (lmul_left R b) :=
by { ext, simp only [lmul_left_apply, linear_map.comp_apply, mul_assoc] }

@[simp] lemma lmul_right_one : lmul_right R (1:A) = linear_map.id :=
by { ext, simp only [linear_map.id_coe, mul_one, id.def, lmul_right_apply] }

@[simp] lemma lmul_right_mul (a b : A) :
  lmul_right R (a * b) = (lmul_right R b).comp (lmul_right R a) :=
by { ext, simp only [lmul_right_apply, linear_map.comp_apply, mul_assoc] }

@[simp] lemma lmul_left_zero_eq_zero :
  lmul_left R (0 : A) = 0 :=
(lmul R A).map_zero

@[simp] lemma lmul_right_zero_eq_zero :
  lmul_right R (0 : A) = 0 :=
(lmul R A).to_linear_map.flip.map_zero

@[simp] lemma lmul_left_eq_zero_iff (a : A) :
  lmul_left R a = 0 ↔ a = 0 :=
begin
  split; intros h,
  { rw [← mul_one a, ← lmul_left_apply a 1, h, linear_map.zero_apply], },
  { rw h, exact lmul_left_zero_eq_zero, },
end

@[simp] lemma lmul_right_eq_zero_iff (a : A) :
  lmul_right R a = 0 ↔ a = 0 :=
begin
  split; intros h,
  { rw [← one_mul a, ← lmul_right_apply a 1, h, linear_map.zero_apply], },
  { rw h, exact lmul_right_zero_eq_zero, },
end

@[simp] lemma pow_lmul_left (a : A) (n : ℕ) :
  (lmul_left R a) ^ n = lmul_left R (a ^ n) :=
((lmul R A).map_pow a n).symm

@[simp] lemma pow_lmul_right (a : A) (n : ℕ) :
  (lmul_right R a) ^ n = lmul_right R (a ^ n) :=
linear_map.coe_injective $ ((lmul_right R a).coe_pow n).symm ▸ (mul_right_iterate a n)

end

section

variables {R A : Type*} [comm_semiring R] [ring A] [algebra R A]

lemma lmul_left_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (lmul_left R x) :=
by { letI : is_domain A := { exists_pair_ne := ⟨x, 0, hx⟩, ..‹ring A›, ..‹no_zero_divisors A› },
     exact mul_right_injective₀ hx }

lemma lmul_right_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (lmul_right R x) :=
by { letI : is_domain A := { exists_pair_ne := ⟨x, 0, hx⟩, ..‹ring A›, ..‹no_zero_divisors A› },
     exact mul_left_injective₀ hx }

lemma lmul_injective [no_zero_divisors A] {x : A} (hx : x ≠ 0) :
  function.injective (lmul R A x) :=
by { letI : is_domain A := { exists_pair_ne := ⟨x, 0, hx⟩, ..‹ring A›, ..‹no_zero_divisors A› },
     exact mul_right_injective₀ hx }

end

end algebra

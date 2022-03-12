/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.algebra.basic
import linear_algebra.prod
import algebra.non_unital_alg_hom

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `algebra.unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `algebra.unitization R A` given by `λ a, (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `algebra.unitization R A` to `B`.

## Main definitions

* `algebra.unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `unitization.coe_non_unital_alg_hom`: coercion as a non-unital algebra homomorphism.
* `non_unital_alg_hom.to_alg_hom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `algebra.unitization R A →ₐ[R] B`.

## Main results

* `non_unital_alg_hom.to_alg_hom_unique`: the extension is unique

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/

/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a type synonym for
`R × A`.-/
def algebra.unitization (R A : Type*) := R × A

instance unitization.inhabited (R A : Type*) [inhabited R] [inhabited A] :
  inhabited (algebra.unitization R A) :=
{ default := (default, default) }

open algebra

namespace unitization

section basic

variables {R A : Type*}

/-- The canonical inclusion `R → unitization R A`. -/
def inl [has_zero A] (r : R) : unitization R A :=
(r, 0)

/-- The canonical inclusion `A → unitization R A`. -/
def inr [has_zero R] (a : A) : unitization R A :=
(0, a)

/-- The canonical projection `unitization R A → R`. -/
def fst (x : unitization R A) : R :=
x.1

/-- The canonical projection `unitization R A → A`. -/
def snd (x : unitization R A) : A :=
x.2

@[ext] lemma ext {x y : unitization R A} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
prod.ext h1 h2

section
variables (A)
@[simp] lemma fst_inl [has_zero A] (r : R) : (inl r : unitization R A).fst = r := rfl
@[simp] lemma snd_inl [has_zero A] (r : R) : (inl r : unitization R A).snd = 0 := rfl
end

section
variables (R)
@[simp] lemma fst_inr [has_zero R] (a : A) : (inr a : unitization R A).fst = 0 := rfl
@[simp] lemma snd_inr [has_zero R] (a : A) : (inr a : unitization R A).snd = a := rfl
end

lemma inl_injective [has_zero A] : function.injective (inl : R → unitization R A) :=
function.left_inverse.injective $ fst_inl _

lemma inr_injective [has_zero R] : function.injective (inr : A → unitization R A) :=
function.left_inverse.injective $ snd_inr _

end basic

/-! ### Structures inherited from `prod`

Additive operators and scalar multiplication operate elementwise. -/

section additive

variables {T : Type*} {S : Type*} {R : Type*} {A : Type*}

instance [inhabited R] [inhabited A] : inhabited (unitization R A) :=
prod.inhabited

instance [has_zero R] [has_zero A] : has_zero (unitization R A) :=
prod.has_zero

instance [has_add R] [has_add A] : has_add (unitization R A) :=
prod.has_add

instance [has_neg R] [has_neg A] : has_neg (unitization R A) :=
prod.has_neg

instance [add_semigroup R] [add_semigroup A] : add_semigroup (unitization R A) :=
prod.add_semigroup

instance [add_zero_class R] [add_zero_class A] : add_zero_class (unitization R A) :=
prod.add_zero_class

instance [add_monoid R] [add_monoid A] : add_monoid (unitization R A) :=
prod.add_monoid

instance [add_group R] [add_group A] : add_group (unitization R A) :=
prod.add_group

instance [add_comm_semigroup R] [add_comm_semigroup A] : add_comm_semigroup (unitization R A) :=
prod.add_comm_semigroup

instance [add_comm_monoid R] [add_comm_monoid A] : add_comm_monoid (unitization R A) :=
prod.add_comm_monoid

instance [add_comm_group R] [add_comm_group A] : add_comm_group (unitization R A) :=
prod.add_comm_group

instance [has_scalar S R] [has_scalar S A] : has_scalar S (unitization R A) :=
prod.has_scalar

instance [has_scalar T R] [has_scalar T A] [has_scalar S R] [has_scalar S A] [has_scalar T S]
  [is_scalar_tower T S R] [is_scalar_tower T S A] : is_scalar_tower T S (unitization R A) :=
prod.is_scalar_tower

instance [has_scalar T R] [has_scalar T A] [has_scalar S R] [has_scalar S A]
  [smul_comm_class T S R] [smul_comm_class T S A] : smul_comm_class T S (unitization R A) :=
prod.smul_comm_class

instance [has_scalar S R] [has_scalar S A] [has_scalar Sᵐᵒᵖ R] [has_scalar Sᵐᵒᵖ A]
  [is_central_scalar S R] [is_central_scalar S A] : is_central_scalar S (unitization R A) :=
prod.is_central_scalar

instance [monoid S] [mul_action S R] [mul_action S A] : mul_action S (unitization R A) :=
prod.mul_action

instance [monoid S] [add_monoid R] [add_monoid A]
  [distrib_mul_action S R] [distrib_mul_action S A] : distrib_mul_action S (unitization R A) :=
prod.distrib_mul_action

instance [semiring S] [add_comm_monoid R] [add_comm_monoid A]
  [module S R] [module S A] : module S (unitization R A) :=
prod.module

@[simp] lemma fst_zero [has_zero R] [has_zero A] : (0 : unitization R A).fst = 0 := rfl
@[simp] lemma snd_zero [has_zero R] [has_zero A] : (0 : unitization R A).snd = 0 := rfl

@[simp] lemma fst_add [has_add R] [has_add A] (x₁ x₂ : unitization R A) :
  (x₁ + x₂).fst = x₁.fst + x₂.fst := rfl
@[simp] lemma snd_add [has_add R] [has_add A] (x₁ x₂ : unitization R A) :
  (x₁ + x₂).snd = x₁.snd + x₂.snd := rfl

@[simp] lemma fst_neg [has_neg R] [has_neg A] (x : unitization R A) : (-x).fst = -x.fst := rfl
@[simp] lemma snd_neg [has_neg R] [has_neg A] (x : unitization R A) : (-x).snd = -x.snd := rfl

@[simp] lemma fst_smul [has_scalar S R] [has_scalar S A] (s : S) (x : unitization R A) :
  (s • x).fst = s • x.fst := rfl
@[simp] lemma snd_smul [has_scalar S R] [has_scalar S A] (s : S) (x : unitization R A) :
  (s • x).snd = s • x.snd := rfl

section
variables (A)

@[simp] lemma inl_zero [has_zero R] [has_zero A] : (inl 0 : unitization R A) = 0 := rfl

@[simp] lemma inl_add [has_add R] [add_zero_class A] (r₁ r₂ : R) :
  (inl (r₁ + r₂) : unitization R A) = inl r₁ + inl r₂ :=
ext rfl (add_zero 0).symm

@[simp] lemma inl_neg [has_neg R] [add_group A] (r : R) :
  (inl (-r) : unitization R A) = -inl r :=
ext rfl neg_zero.symm

@[simp] lemma inl_smul [monoid S] [add_monoid A] [has_scalar S R] [distrib_mul_action S A]
  (s : S) (r : R) : (inl (s • r) : unitization R A) = s • inl r :=
ext rfl (smul_zero s).symm

end

section
variables (R)

@[simp] lemma inr_zero [has_zero R] [has_zero A] : (inr 0 : unitization R A) = 0 := rfl

@[simp] lemma inr_add [add_zero_class R] [add_zero_class A] (m₁ m₂ : A) :
  (inr (m₁ + m₂) : unitization R A) = inr m₁ + inr m₂ :=
ext (add_zero 0).symm rfl

@[simp] lemma inr_neg [add_group R] [has_neg A] (m : A) :
  (inr (-m) : unitization R A) = -inr m :=
ext neg_zero.symm rfl

@[simp] lemma inr_smul [has_zero R] [has_zero S] [smul_with_zero S R] [has_scalar S A]
  (r : S) (m : A) : (inr (r • m) : unitization R A) = r • inr m :=
ext (smul_zero' _ _).symm rfl

end

lemma inl_fst_add_inr_snd_eq [add_zero_class R] [add_zero_class A] (x : unitization R A) :
  inl x.fst + inr x.snd = x :=
ext (add_zero x.1) (zero_add x.2)

/-- To show a property hold on all `unitization R A` it suffices to show it holds
on terms of the form `inl r + inr m`.

This can be used as `induction x using unitization.ind`. -/
lemma ind {R A} [add_zero_class R] [add_zero_class A] {P : unitization R A → Prop}
  (h : ∀ r a, P (inl r + inr a)) (x) : P x :=
inl_fst_add_inr_snd_eq x ▸ h x.1 x.2

/-- This cannot be marked `@[ext]` as it ends up being used instead of `linear_map.prod_ext` when
working with `R × A`. -/
lemma linear_map_ext {N} [semiring S] [add_comm_monoid R] [add_comm_monoid A] [add_comm_monoid N]
  [module S R] [module S A] [module S N] ⦃f g : unitization R A →ₗ[S] N⦄
  (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a, f (inr a) = g (inr a)) :
  f = g :=
linear_map.prod_ext (linear_map.ext hl) (linear_map.ext hr)

variables (R A)

/-- The canonical `R`-linear inclusion `A → unitization R A`. -/
@[simps apply]
def inr_hom [semiring R] [add_comm_monoid A] [module R A] : A →ₗ[R] unitization R A :=
{ to_fun := inr, ..linear_map.inr R R A }

/-- The canonical `R`-linear projection `unitization R A → A`. -/
@[simps apply]
def snd_hom [semiring R] [add_comm_monoid A] [module R A] : unitization R A →ₗ[R] A :=
{ to_fun := snd, ..linear_map.snd _ _ _ }

end additive

/-! ### Multiplicative structure -/

section mul
variables {R A : Type*}

instance [has_one R] [has_zero A] : has_one (unitization R A) :=
⟨(1, 0)⟩

instance [has_mul R] [has_add A] [has_mul A] [has_scalar R A] : has_mul (unitization R A) :=
⟨λ x y, (x.1 * y.1, x.1 • y.2 + y.1 • x.2 + x.2 * y.2)⟩

@[simp] lemma fst_one [has_one R] [has_zero A] : (1 : unitization R A).fst = 1 := rfl
@[simp] lemma snd_one [has_one R] [has_zero A] : (1 : unitization R A).snd = 0 := rfl

@[simp] lemma fst_mul [has_mul R] [has_add A] [has_mul A] [has_scalar R A]
  (x₁ x₂ : unitization R A) : (x₁ * x₂).fst = x₁.fst * x₂.fst := rfl
@[simp] lemma snd_mul [has_mul R] [has_add A] [has_mul A] [has_scalar R A]
  (x₁ x₂ : unitization R A) : (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
rfl

section
variables (A)

@[simp] lemma inl_one [has_one R] [has_zero A] : (inl 1 : unitization R A) = 1 := rfl

@[simp] lemma inl_mul [monoid R] [non_unital_semiring A] [distrib_mul_action R A]
  (r₁ r₂ : R) : (inl (r₁ * r₂) : unitization R A) = inl r₁ * inl r₂ :=
ext rfl $ show (0 : A) = r₁ • (0 : A) + r₂ • 0 + 0 * 0, by simp only [smul_zero, add_zero, mul_zero]

lemma inl_mul_inl [monoid R] [non_unital_semiring A] [distrib_mul_action R A] (r₁ r₂ : R) :
  (inl r₁ * inl r₂ : unitization R A) = inl (r₁ * r₂) :=
(inl_mul A r₁ r₂).symm

end

section
variables (R)

@[simp] lemma inr_mul_inr [semiring R] [non_unital_semiring A] [module R A] (a₁ a₂ : A) :
  (inr a₁ * inr a₂ : unitization R A) = inr (a₁ * a₂) :=
ext (mul_zero _) $ show (0 : R) • a₂ + (0 : R) • a₁ + a₁ * a₂ = a₁ * a₂,
  by simp only [zero_smul, zero_add]

end

lemma inl_mul_inr [semiring R] [non_unital_semiring A] [module R A] (r : R) (a : A) :
  (inl r * inr a : unitization R A) = inr (r • a) :=
ext (mul_zero r) $ show r • a + (0 : R) • 0 + 0 * a = r • a,
  by rw [smul_zero, add_zero, zero_mul, add_zero]

lemma inr_mul_inl [semiring R] [non_unital_semiring A] [module R A] (r : R) (a : A) :
  (inr a * inl r : unitization R A) = inr (r • a) :=
ext (zero_mul r) $ show (0 : R) • 0 + r • a + a * 0 = r • a,
  by rw [smul_zero, zero_add, mul_zero, add_zero]

instance [monoid R] [non_unital_semiring A] [distrib_mul_action R A] :
  mul_one_class (unitization R A) :=
{ one_mul := λ x, ext (one_mul x.1) $ show (1 : R) • x.2 + x.1 • 0 + 0 * x.2 = x.2,
    by rw [one_smul, smul_zero, add_zero, zero_mul, add_zero],
  mul_one := λ x, ext (mul_one x.1) $ show (x.1 • 0 : A) + (1 : R) • x.2 + x.2 * 0 = x.2,
    by rw [smul_zero, zero_add, one_smul, mul_zero, add_zero],
  .. unitization.has_one,
  .. unitization.has_mul }

instance [semiring R] [non_unital_semiring A] [module R A] :
  non_assoc_semiring (unitization R A) :=
{ zero_mul := λ x, ext (zero_mul x.1) $ show (0 : R) • x.2 + x.1 • 0 + 0 * x.2 = 0,
    by rw [zero_smul, zero_add, smul_zero, zero_mul, add_zero],
  mul_zero := λ x, ext (mul_zero x.1) $ show (x.1 • 0 : A) + (0 : R) • x.2 + x.2 * 0 = 0,
    by rw [smul_zero, zero_add, zero_smul, mul_zero, add_zero],
  left_distrib := λ x₁ x₂ x₃, ext (mul_add x₁.1 x₂.1 x₃.1) $
    show x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 + x₁.2 * (x₂.2 + x₃.2) =
      x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2),
    by { rw [smul_add, add_smul, mul_add], ac_refl },
  right_distrib := λ x₁ x₂ x₃, ext (add_mul x₁.1 x₂.1 x₃.1) $
    show (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) + (x₁.2 + x₂.2) * x₃.2 =
      x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2 + x₂.2 * x₃.2),
    by { rw [add_smul, smul_add, add_mul], ac_refl },
  .. unitization.mul_one_class,
  .. unitization.add_comm_monoid }

.

instance [comm_monoid R] [non_unital_semiring A] [distrib_mul_action R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : monoid (unitization R A) :=
{ mul_assoc := λ x y z, ext (mul_assoc x.1 y.1 z.1) $
    show (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) +
      (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) * z.2 =
      x.1 • (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) + (y.1 * z.1) • x.2 +
      x.2 * (y.1 • z.2 + z.1 • y.2 + y.2 * z.2),
    by { simp only [smul_add, mul_add, add_mul, smul_smul, smul_mul_assoc, mul_comm z.fst,
           mul_smul_comm, mul_assoc],
         abel },
  ..unitization.mul_one_class }

-- This should work for `non_unital_comm_semiring`s, but we don't seem to have those
instance [comm_monoid R] [comm_semiring A] [distrib_mul_action R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : comm_monoid (unitization R A) :=
{ mul_comm := λ x₁ x₂, ext (mul_comm x₁.1 x₂.1) $
    show x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 + x₂.2 * x₁.2,
    by rw [add_comm (x₁.1 • x₂.2), mul_comm],
  ..unitization.monoid }

instance [comm_semiring R] [non_unital_semiring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : semiring (unitization R A) :=
{ ..unitization.monoid,
  ..unitization.non_assoc_semiring }

-- This should work for `non_unital_comm_semiring`s, but we don't seem to have those
instance [comm_semiring R] [comm_semiring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : comm_semiring (unitization R A) :=
{ ..unitization.comm_monoid,
  ..unitization.non_assoc_semiring }

variables (R A)

/-- The canonical inclusion of rings `R →+* unitization R A`. -/
@[simps apply]
def inl_ring_hom [semiring R] [non_unital_semiring A] [module R A] : R →+* unitization R A :=
{ to_fun := inl,
  map_one' := inl_one A,
  map_mul' := inl_mul A,
  map_zero' := inl_zero A,
  map_add' := inl_add A }

end mul

section algebra
variables (R A : Type*)
variables [comm_semiring R] [non_unital_semiring A]
variables [module R A] [is_scalar_tower R A A] [smul_comm_class R A A]

instance algebra : algebra R (unitization R A) :=
{ commutes' := λ r x,
  begin
    induction x using unitization.ind,
    simp only [ring_hom.to_fun_eq_coe, inl_ring_hom_apply, mul_add, add_mul, inl_mul_inl],
    rw [inl_mul_inr, inr_mul_inl, mul_comm]
  end,
  smul_def' := λ r x,
  begin
    induction x using unitization.ind,
    simp only [mul_add, inl_mul_inr, smul_add, ring_hom.to_fun_eq_coe, inl_ring_hom_apply,
      inr_smul],
    rw [inl_mul_inl, ←smul_eq_mul, inl_smul],
  end,
  ..(unitization.inl_ring_hom R A) }

lemma algebra_map_eq_inl : ⇑(algebra_map R (unitization R A)) = inl := rfl
lemma algebra_map_eq_inl_hom : algebra_map R (unitization R A) = inl_ring_hom R A := rfl

/-- The canonical `R`-algebra projection `unitization R A → R`. -/
@[simps]
def fst_hom : unitization R A →ₐ[R] R :=
{ to_fun := fst,
  map_one' := fst_one,
  map_mul' := fst_mul,
  map_zero' := fst_zero,
  map_add' := fst_add,
  commutes' := fst_inl A }

end algebra

section coe
variables {R A : Type*}

instance [has_zero R] : has_coe_t A (unitization R A) := { coe := inr }

@[simp]
lemma coe_apply [has_zero R] (a : A) : (a : unitization R A) = inr a := rfl

lemma coe_injective [has_zero R] : function.injective (coe : A → unitization R A) :=
inr_injective

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `algebra.unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def coe_non_unital_alg_hom [comm_semiring R] [non_unital_semiring A] [module R A] :
  non_unital_alg_hom R A (unitization R A) :=
{ to_fun := coe,
  map_smul' := by simp,
  map_zero' := by simp,
  map_add' := by simp,
  map_mul' := by simp }

end coe

end unitization

section alg_hom

open unitization

variables
{R A : Type*}
[comm_semiring R] [non_unital_semiring A]
[module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
{B : Type*} [ring B] [algebra R B]

/-- The extension to `unitization R A →ₐ[R] B` of a non-unital algebra homomorphism `φ : A → B`
from a non-unital `R`-algebra `A` into a unital `R`-algebra `B`. -/
@[simps]
def non_unital_alg_hom.to_alg_hom (φ : non_unital_alg_hom R A B) : (unitization R A) →ₐ[R] B :=
{ to_fun := λ x, algebra_map R B x.fst + φ x.snd,
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero],
  map_mul' := λ x y,
  begin
    induction x using unitization.ind,
    induction y using unitization.ind,
    simp only [mul_add, add_mul, inr_mul_inr, fst_add, fst_mul, fst_inl, fst_inr, mul_zero,
      add_zero, zero_mul, map_mul, snd_add, snd_mul, snd_inl, smul_zero, snd_inr, zero_add,
      φ.map_add, φ.map_smul, φ.map_mul],
    rw ←algebra.commutes _ (φ x_a),
    simp only [algebra_map_eq_smul_one, smul_one_mul, add_assoc],
  end,
  map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero],
  map_add' := λ x y,
  begin
    induction x using unitization.ind,
    induction y using unitization.ind,
    simp only [fst_add, fst_inl, fst_inr, add_zero, map_add, snd_add, snd_inl, snd_inr, zero_add,
      φ.map_add],
    rw add_add_add_comm,
  end,
  commutes' := λ r, by simp only [algebra_map_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero] }

local postfix `¹`:std.prec.max_plus := non_unital_alg_hom.to_alg_hom

lemma non_unital_alg_hom.to_alg_hom_apply_coe (φ : non_unital_alg_hom R A B) (a : A) : φ¹ a = φ a :=
by simp only [coe_apply, φ.to_alg_hom_apply, fst_inr, map_zero, snd_inr, zero_add]

lemma non_unital_alg_hom.to_alg_hom_unique (φ : non_unital_alg_hom R A B)
  (ψ : unitization R A →ₐ[R] B) (h : ∀ a : A, ψ a = φ¹ a) : ψ = φ¹ :=
begin
  ext,
  induction x using unitization.ind,
  simp only [map_add, ←algebra_map_eq_inl, ←coe_apply, h, alg_hom.commutes],
end

end alg_hom

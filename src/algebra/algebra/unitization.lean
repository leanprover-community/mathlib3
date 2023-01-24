/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.algebra.basic
import linear_algebra.prod
import algebra.hom.non_unital_alg

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

There is a natural coercion from `A` to `unitization R A` given by `λ a, (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `unitization R A` to `B`.

## Main definitions

* `unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `unitization.coe_non_unital_alg_hom`: coercion as a non-unital algebra homomorphism.
* `non_unital_alg_hom.to_alg_hom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `unitization R A →ₐ[R] B`.

## Main results

* `non_unital_alg_hom.to_alg_hom_unique`: the extension is unique

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/

/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a type synonym for
`R × A`.-/
def unitization (R A : Type*) := R × A

namespace unitization

section basic

variables {R A : Type*}

/-- The canonical inclusion `R → unitization R A`. -/
def inl [has_zero A] (r : R) : unitization R A :=
(r, 0)

/-- The canonical inclusion `A → unitization R A`. -/
instance [has_zero R] : has_coe_t A (unitization R A) := { coe := λ a, (0, a) }

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
@[simp] lemma fst_coe [has_zero R] (a : A) : (a : unitization R A).fst = 0 := rfl
@[simp] lemma snd_coe [has_zero R] (a : A) : (a : unitization R A).snd = a := rfl
end

lemma inl_injective [has_zero A] : function.injective (inl : R → unitization R A) :=
function.left_inverse.injective $ fst_inl _

lemma coe_injective [has_zero R] : function.injective (coe : A → unitization R A) :=
function.left_inverse.injective $ snd_coe _

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

instance [has_smul S R] [has_smul S A] : has_smul S (unitization R A) :=
prod.has_smul

instance [has_smul T R] [has_smul T A] [has_smul S R] [has_smul S A] [has_smul T S]
  [is_scalar_tower T S R] [is_scalar_tower T S A] : is_scalar_tower T S (unitization R A) :=
prod.is_scalar_tower

instance [has_smul T R] [has_smul T A] [has_smul S R] [has_smul S A]
  [smul_comm_class T S R] [smul_comm_class T S A] : smul_comm_class T S (unitization R A) :=
prod.smul_comm_class

instance [has_smul S R] [has_smul S A] [has_smul Sᵐᵒᵖ R] [has_smul Sᵐᵒᵖ A]
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

@[simp] lemma fst_smul [has_smul S R] [has_smul S A] (s : S) (x : unitization R A) :
  (s • x).fst = s • x.fst := rfl
@[simp] lemma snd_smul [has_smul S R] [has_smul S A] (s : S) (x : unitization R A) :
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

@[simp] lemma inl_smul [monoid S] [add_monoid A] [has_smul S R] [distrib_mul_action S A]
  (s : S) (r : R) : (inl (s • r) : unitization R A) = s • inl r :=
ext rfl (smul_zero s).symm

end

section
variables (R)

@[simp] lemma coe_zero [has_zero R] [has_zero A] : ↑(0 : A) = (0 : unitization R A) := rfl

@[simp] lemma coe_add [add_zero_class R] [has_add A] (m₁ m₂ : A) :
  (↑(m₁ + m₂) : unitization R A)  = m₁ + m₂ :=
ext (add_zero 0).symm rfl

@[simp] lemma coe_neg [add_group R] [has_neg A] (m : A) :
  (↑(-m) : unitization R A) = -m :=
ext neg_zero.symm rfl

@[simp] lemma coe_smul [has_zero R] [has_zero S] [smul_with_zero S R] [has_smul S A]
  (r : S) (m : A) : (↑(r • m) : unitization R A) = r • m :=
ext (smul_zero _).symm rfl

end

lemma inl_fst_add_coe_snd_eq [add_zero_class R] [add_zero_class A] (x : unitization R A) :
  inl x.fst + ↑x.snd = x :=
ext (add_zero x.1) (zero_add x.2)

/-- To show a property hold on all `unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x using unitization.ind`. -/
lemma ind {R A} [add_zero_class R] [add_zero_class A] {P : unitization R A → Prop}
  (h : ∀ (r : R) (a : A), P (inl r + a)) (x) : P x :=
inl_fst_add_coe_snd_eq x ▸ h x.1 x.2

/-- This cannot be marked `@[ext]` as it ends up being used instead of `linear_map.prod_ext` when
working with `R × A`. -/
lemma linear_map_ext {N} [semiring S] [add_comm_monoid R] [add_comm_monoid A] [add_comm_monoid N]
  [module S R] [module S A] [module S N] ⦃f g : unitization R A →ₗ[S] N⦄
  (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a : A, f a = g a) :
  f = g :=
linear_map.prod_ext (linear_map.ext hl) (linear_map.ext hr)

variables (R A)

/-- The canonical `R`-linear inclusion `A → unitization R A`. -/
@[simps apply]
def coe_hom [semiring R] [add_comm_monoid A] [module R A] : A →ₗ[R] unitization R A :=
{ to_fun := coe, ..linear_map.inr R R A }

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

instance [has_mul R] [has_add A] [has_mul A] [has_smul R A] : has_mul (unitization R A) :=
⟨λ x y, (x.1 * y.1, x.1 • y.2 + y.1 • x.2 + x.2 * y.2)⟩

@[simp] lemma fst_one [has_one R] [has_zero A] : (1 : unitization R A).fst = 1 := rfl
@[simp] lemma snd_one [has_one R] [has_zero A] : (1 : unitization R A).snd = 0 := rfl

@[simp] lemma fst_mul [has_mul R] [has_add A] [has_mul A] [has_smul R A]
  (x₁ x₂ : unitization R A) : (x₁ * x₂).fst = x₁.fst * x₂.fst := rfl
@[simp] lemma snd_mul [has_mul R] [has_add A] [has_mul A] [has_smul R A]
  (x₁ x₂ : unitization R A) : (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
rfl

section
variables (A)

@[simp] lemma inl_one [has_one R] [has_zero A] : (inl 1 : unitization R A) = 1 := rfl

@[simp] lemma inl_mul [monoid R] [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  (r₁ r₂ : R) : (inl (r₁ * r₂) : unitization R A) = inl r₁ * inl r₂ :=
ext rfl $ show (0 : A) = r₁ • (0 : A) + r₂ • 0 + 0 * 0, by simp only [smul_zero, add_zero, mul_zero]

lemma inl_mul_inl [monoid R] [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  (r₁ r₂ : R) : (inl r₁ * inl r₂ : unitization R A) = inl (r₁ * r₂) :=
(inl_mul A r₁ r₂).symm

end

section
variables (R)

@[simp] lemma coe_mul [semiring R] [add_comm_monoid A] [has_mul A] [smul_with_zero R A]
  (a₁ a₂ : A) : (↑(a₁ * a₂) : unitization R A) = a₁ * a₂ :=
ext (mul_zero _).symm $ show a₁ * a₂ = (0 : R) • a₂ + (0 : R) • a₁ + a₁ * a₂,
  by simp only [zero_smul, zero_add]

end

lemma inl_mul_coe [semiring R] [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  (r : R) (a : A) : (inl r * a : unitization R A) = ↑(r • a) :=
ext (mul_zero r) $ show r • a + (0 : R) • 0 + 0 * a = r • a,
  by rw [smul_zero, add_zero, zero_mul, add_zero]

lemma coe_mul_inl [semiring R] [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  (r : R) (a : A) : (a * inl r : unitization R A) = ↑(r • a) :=
ext (zero_mul r) $ show (0 : R) • 0 + r • a + a * 0 = r • a,
  by rw [smul_zero, zero_add, mul_zero, add_zero]

instance mul_one_class [monoid R] [non_unital_non_assoc_semiring A] [distrib_mul_action R A] :
  mul_one_class (unitization R A) :=
{ one_mul := λ x, ext (one_mul x.1) $ show (1 : R) • x.2 + x.1 • 0 + 0 * x.2 = x.2,
    by rw [one_smul, smul_zero, add_zero, zero_mul, add_zero],
  mul_one := λ x, ext (mul_one x.1) $ show (x.1 • 0 : A) + (1 : R) • x.2 + x.2 * 0 = x.2,
    by rw [smul_zero, zero_add, one_smul, mul_zero, add_zero],
  .. unitization.has_one,
  .. unitization.has_mul }

instance [semiring R] [non_unital_non_assoc_semiring A] [module R A] :
  non_assoc_semiring (unitization R A) :=
{ zero_mul := λ x, ext (zero_mul x.1) $ show (0 : R) • x.2 + x.1 • 0 + 0 * x.2 = 0,
    by rw [zero_smul, zero_add, smul_zero, zero_mul, add_zero],
  mul_zero := λ x, ext (mul_zero x.1) $ show (x.1 • 0 : A) + (0 : R) • x.2 + x.2 * 0 = 0,
    by rw [smul_zero, zero_add, zero_smul, mul_zero, add_zero],
  left_distrib := λ x₁ x₂ x₃, ext (mul_add x₁.1 x₂.1 x₃.1) $
    show x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 + x₁.2 * (x₂.2 + x₃.2) =
      x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2),
    by { simp only [smul_add, add_smul, mul_add], abel },
  right_distrib := λ x₁ x₂ x₃, ext (add_mul x₁.1 x₂.1 x₃.1) $
    show (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) + (x₁.2 + x₂.2) * x₃.2 =
      x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2 + x₂.2 * x₃.2),
    by { simp only [add_smul, smul_add, add_mul], abel },
  .. unitization.mul_one_class,
  .. unitization.add_comm_monoid }

instance [comm_monoid R] [non_unital_semiring A] [distrib_mul_action R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : monoid (unitization R A) :=
{ mul_assoc := λ x y z, ext (mul_assoc x.1 y.1 z.1) $
    show (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) +
      (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) * z.2 =
      x.1 • (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) + (y.1 * z.1) • x.2 +
      x.2 * (y.1 • z.2 + z.1 • y.2 + y.2 * z.2),
    { simp only [smul_add, mul_add, add_mul, smul_smul, smul_mul_assoc, mul_smul_comm, mul_assoc],
      nth_rewrite 1 mul_comm,
      nth_rewrite 2 mul_comm,
      abel },
  ..unitization.mul_one_class }

instance [comm_monoid R] [non_unital_comm_semiring A] [distrib_mul_action R A]
  [is_scalar_tower R A A] [smul_comm_class R A A] : comm_monoid (unitization R A) :=
{ mul_comm := λ x₁ x₂, ext (mul_comm x₁.1 x₂.1) $
    show x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 + x₂.2 * x₁.2,
    by rw [add_comm (x₁.1 • x₂.2), mul_comm],
  ..unitization.monoid }

instance [comm_semiring R] [non_unital_semiring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : semiring (unitization R A) :=
{ ..unitization.monoid,
  ..unitization.non_assoc_semiring }

instance [comm_semiring R] [non_unital_comm_semiring A] [module R A] [is_scalar_tower R A A]
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

/-! ### Star structure -/

section star

variables {R A : Type*}

instance [has_star R] [has_star A] : has_star (unitization R A) :=
⟨λ ra, (star ra.fst, star ra.snd)⟩

@[simp] lemma fst_star [has_star R] [has_star A] (x : unitization R A) :
  (star x).fst = star x.fst := rfl

@[simp] lemma snd_star [has_star R] [has_star A] (x : unitization R A) :
  (star x).snd = star x.snd := rfl

@[simp] lemma inl_star [has_star R] [add_monoid A] [star_add_monoid A] (r : R) :
  inl (star r) = star (inl r : unitization R A) :=
ext rfl (by simp only [snd_star, star_zero, snd_inl])

@[simp] lemma coe_star [add_monoid R] [star_add_monoid R] [has_star A] (a : A) :
  ↑(star a) = star (a : unitization R A) :=
ext (by simp only [fst_star, star_zero, fst_coe]) rfl

instance [add_monoid R] [add_monoid A] [star_add_monoid R] [star_add_monoid A] :
  star_add_monoid (unitization R A) :=
{ star_involutive := λ x, ext (star_star x.fst) (star_star x.snd),
  star_add := λ x y, ext (star_add x.fst y.fst) (star_add x.snd y.snd) }

instance [comm_semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A]
  [module R A] [star_module R A] : star_module R (unitization R A) :=
{ star_smul := λ r x, ext (by simp) (by simp) }

instance [comm_semiring R] [star_ring R] [non_unital_semiring A] [star_ring A]
  [module R A] [is_scalar_tower R A A] [smul_comm_class R A A] [star_module R A] :
  star_ring (unitization R A) :=
{ star_mul := λ x y, ext (by simp [star_mul])
    (by simp [star_mul, add_comm (star x.fst • star y.snd)]),
  ..unitization.star_add_monoid }

end star

/-! ### Algebra structure -/

section algebra
variables (S R A : Type*)
[comm_semiring S] [comm_semiring R] [non_unital_semiring A]
[module R A] [is_scalar_tower R A A] [smul_comm_class R A A]
[algebra S R] [distrib_mul_action S A] [is_scalar_tower S R A]

instance algebra : algebra S (unitization R A) :=
{ commutes' := λ r x,
  begin
    induction x using unitization.ind,
    simp only [mul_add, add_mul, ring_hom.to_fun_eq_coe, ring_hom.coe_comp, function.comp_app,
      inl_ring_hom_apply, inl_mul_inl],
    rw [inl_mul_coe, coe_mul_inl, mul_comm]
  end,
  smul_def' := λ s x,
  begin
    induction x using unitization.ind,
    simp only [mul_add, smul_add, ring_hom.to_fun_eq_coe, ring_hom.coe_comp, function.comp_app,
      inl_ring_hom_apply, algebra.algebra_map_eq_smul_one],
    rw [inl_mul_inl, inl_mul_coe, smul_one_mul, inl_smul, coe_smul, smul_one_smul]
  end,
  ..(unitization.inl_ring_hom R A).comp (algebra_map S R) }

lemma algebra_map_eq_inl_comp : ⇑(algebra_map S (unitization R A)) = inl ∘ algebra_map S R := rfl
lemma algebra_map_eq_inl_ring_hom_comp :
  algebra_map S (unitization R A) = (inl_ring_hom R A).comp (algebra_map S R) := rfl
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

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def coe_non_unital_alg_hom (R A : Type*) [comm_semiring R] [non_unital_semiring A] [module R A] :
  A →ₙₐ[R] unitization R A :=
{ to_fun := coe,
  map_smul' := coe_smul R,
  map_zero' := coe_zero R,
  map_add' := coe_add R,
  map_mul' := coe_mul R }

end coe

section alg_hom

variables {S R A : Type*}
  [comm_semiring S] [comm_semiring R] [non_unital_semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
  {B : Type*} [semiring B] [algebra S B]
  [algebra S R] [distrib_mul_action S A] [is_scalar_tower S R A]
  {C : Type*} [ring C] [algebra R C]

lemma alg_hom_ext {φ ψ : unitization R A →ₐ[S] B} (h : ∀ a : A, φ a = ψ a)
  (h' : ∀ r, φ (algebra_map R (unitization R A) r) = ψ (algebra_map R (unitization R A) r)) :
  φ = ψ :=
begin
  ext,
  induction x using unitization.ind,
  simp only [map_add, ←algebra_map_eq_inl, h, h'],
end

/-- See note [partially-applied ext lemmas] -/
@[ext]
lemma alg_hom_ext' {φ ψ : unitization R A →ₐ[R] C}
  (h : φ.to_non_unital_alg_hom.comp (coe_non_unital_alg_hom R A) =
    ψ.to_non_unital_alg_hom.comp (coe_non_unital_alg_hom R A)) :
  φ = ψ :=
alg_hom_ext (non_unital_alg_hom.congr_fun h) (by simp [alg_hom.commutes])

/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps apply_apply]
def lift : (A →ₙₐ[R] C) ≃ (unitization R A →ₐ[R] C) :=
{ to_fun := λ φ,
  { to_fun := λ x, algebra_map R C x.fst + φ x.snd,
    map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero],
    map_mul' := λ x y,
    begin
      induction x using unitization.ind,
      induction y using unitization.ind,
      simp only [mul_add, add_mul, coe_mul, fst_add, fst_mul, fst_inl, fst_coe, mul_zero,
        add_zero, zero_mul, map_mul, snd_add, snd_mul, snd_inl, smul_zero, snd_coe, zero_add,
        φ.map_add, φ.map_smul, φ.map_mul, zero_smul, zero_add],
      rw ←algebra.commutes _ (φ x_a),
      simp only [algebra.algebra_map_eq_smul_one, smul_one_mul, add_assoc],
    end,
    map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero],
    map_add' := λ x y,
    begin
      induction x using unitization.ind,
      induction y using unitization.ind,
      simp only [fst_add, fst_inl, fst_coe, add_zero, map_add, snd_add, snd_inl, snd_coe, zero_add,
        φ.map_add],
      rw add_add_add_comm,
    end,
    commutes' := λ r, by simp only [algebra_map_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero] },
  inv_fun := λ φ, φ.to_non_unital_alg_hom.comp (coe_non_unital_alg_hom R A),
  left_inv := λ φ, by { ext, simp, },
  right_inv := λ φ, unitization.alg_hom_ext' (by { ext, simp }), }

lemma lift_symm_apply (φ : unitization R A →ₐ[R] C) (a : A) :
  unitization.lift.symm φ a = φ a := rfl

end alg_hom

end unitization

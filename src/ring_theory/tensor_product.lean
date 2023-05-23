/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/

import linear_algebra.finite_dimensional
import ring_theory.adjoin.basic
import linear_algebra.direct_sum.finsupp

/-!
# The tensor product of R-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `R` be a (semi)ring and `A` an `R`-algebra.
In this file we:

- Define the `A`-module structure on `A ⊗ M`, for an `R`-module `M`.
- Define the `R`-algebra structure on `A ⊗ B`, for another `R`-algebra `B`.
  and provide the structure isomorphisms
  * `R ⊗[R] A ≃ₐ[R] A`
  * `A ⊗[R] R ≃ₐ[R] A`
  * `A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`

## Main declaration

- `linear_map.base_change A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

## Implementation notes

The heterobasic definitions below such as:
 * `tensor_product.algebra_tensor_module.curry`
 * `tensor_product.algebra_tensor_module.uncurry`
 * `tensor_product.algebra_tensor_module.lcurry`
 * `tensor_product.algebra_tensor_module.lift`
 * `tensor_product.algebra_tensor_module.lift.equiv`
 * `tensor_product.algebra_tensor_module.mk`
 * `tensor_product.algebra_tensor_module.assoc`

are just more general versions of the definitions already in `linear_algebra/tensor_product`. We
could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

universes u v₁ v₂ v₃ v₄

open_locale tensor_product
open tensor_product

namespace tensor_product

variables {R A M N P : Type*}

/-!
### The `A`-module structure on `A ⊗[R] M`
-/

open linear_map
open algebra (lsmul)

namespace algebra_tensor_module

section semiring
variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]
variables [add_comm_monoid N] [module R N]
variables [add_comm_monoid P] [module R P] [module A P] [is_scalar_tower R A P]

lemma smul_eq_lsmul_rtensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R M a).rtensor N x := rfl

/-- Heterobasic version of `tensor_product.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps] def curry (f : (M ⊗[R] N) →ₗ[A] P) : M →ₗ[A] (N →ₗ[R] P) :=
{ to_fun := curry (f.restrict_scalars R),
  map_smul' := λ c x, linear_map.ext $ λ y, f.map_smul c (x ⊗ₜ y),
  .. curry (f.restrict_scalars R) }

lemma restrict_scalars_curry (f : (M ⊗[R] N) →ₗ[A] P) :
  restrict_scalars R (curry f) = curry (f.restrict_scalars R) :=
rfl

/-- Just as `tensor_product.ext` is marked `ext` instead of `tensor_product.ext'`, this is
a better `ext` lemma than `tensor_product.algebra_tensor_module.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext] lemma curry_injective :
  function.injective (curry : (M ⊗ N →ₗ[A] P) → (M →ₗ[A] N →ₗ[R] P)) :=
λ x y h, linear_map.restrict_scalars_injective R $ curry_injective $
  (congr_arg (linear_map.restrict_scalars R) h : _)

theorem ext {g h : (M ⊗[R] N) →ₗ[A] P}
  (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
curry_injective $ linear_map.ext₂ H

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]
variables [add_comm_monoid N] [module R N]
variables [add_comm_monoid P] [module R P] [module A P] [is_scalar_tower R A P]

/-- Heterobasic version of `tensor_product.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps] def lift (f : M →ₗ[A] (N →ₗ[R] P)) : (M ⊗[R] N) →ₗ[A] P :=
{ map_smul' := λ c, show ∀ x : M ⊗[R] N, (lift (f.restrict_scalars R)).comp (lsmul R _ c) x =
      (lsmul R _ c).comp (lift (f.restrict_scalars R)) x,
    from ext_iff.1 $ tensor_product.ext' $ λ x y,
    by simp only [comp_apply, algebra.lsmul_coe, smul_tmul', lift.tmul, coe_restrict_scalars_eq_coe,
        f.map_smul, smul_apply],
  .. lift (f.restrict_scalars R) }

@[simp] lemma lift_tmul (f : M →ₗ[A] (N →ₗ[R] P)) (x : M) (y : N) :
  lift f (x ⊗ₜ y) = f x y :=
rfl

variables (R A M N P)
/-- Heterobasic version of `tensor_product.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps] def uncurry : (M →ₗ[A] (N →ₗ[R] P)) →ₗ[A] ((M ⊗[R] N) →ₗ[A] P) :=
{ to_fun := lift,
  map_add' := λ f g, ext $ λ x y, by simp only [lift_tmul, add_apply],
  map_smul' := λ c f, ext $ λ x y, by simp only [lift_tmul, smul_apply, ring_hom.id_apply] }

/-- Heterobasic version of `tensor_product.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps] def lcurry : ((M ⊗[R] N) →ₗ[A] P) →ₗ[A] (M →ₗ[A] (N →ₗ[R] P)) :=
{ to_fun := curry,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

/-- Heterobasic version of `tensor_product.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
def lift.equiv : (M →ₗ[A] (N →ₗ[R] P)) ≃ₗ[A] ((M ⊗[R] N) →ₗ[A] P) :=
linear_equiv.of_linear (uncurry R A M N P) (lcurry R A M N P)
  (linear_map.ext $ λ f, ext $ λ x y, lift_tmul _ x y)
  (linear_map.ext $ λ f, linear_map.ext $ λ x, linear_map.ext $ λ y, lift_tmul f x y)

variables (R A M N P)
/-- Heterobasic version of `tensor_product.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps] def mk : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
{ map_smul' := λ c x, rfl,
  .. mk R M N }

local attribute [ext] tensor_product.ext

/-- Heterobasic version of `tensor_product.assoc`:

Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`. -/
def assoc : ((M ⊗[A] P) ⊗[R] N) ≃ₗ[A] (M ⊗[A] (P ⊗[R] N)) :=
linear_equiv.of_linear
  (lift $ tensor_product.uncurry A _ _ _ $ comp (lcurry R A _ _ _) $
    tensor_product.mk A M (P ⊗[R] N))
  (tensor_product.uncurry A _ _ _ $ comp (uncurry R A _ _ _) $
    by { apply tensor_product.curry, exact (mk R A _ _) })
  (by { ext, refl, })
  (by { ext, simp only [curry_apply, tensor_product.curry_apply, mk_apply, tensor_product.mk_apply,
              uncurry_apply, tensor_product.uncurry_apply, id_apply, lift_tmul, compr₂_apply,
              restrict_scalars_apply, function.comp_app, to_fun_eq_coe, lcurry_apply,
              linear_map.comp_apply] })

end comm_semiring

end algebra_tensor_module

end tensor_product

namespace linear_map
open tensor_product

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/

section semiring

variables {R A B M N : Type*} [comm_semiring R]
variables [semiring A] [algebra R A] [semiring B] [algebra R B]
variables [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
variables (r : R) (f g : M →ₗ[R] N)

variables (A)

/-- `base_change A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`. -/
def base_change (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
{ to_fun := f.ltensor A,
  map_add' := (f.ltensor A).map_add,
  map_smul' := λ a x,
    show (f.ltensor A) (rtensor M (linear_map.mul R A a) x) =
      (rtensor N ((linear_map.mul R A) a)) ((ltensor A f) x),
    by { rw [← comp_apply, ← comp_apply],
      simp only [ltensor_comp_rtensor, rtensor_comp_ltensor] } }

variables {A}

@[simp] lemma base_change_tmul (a : A) (x : M) :
  f.base_change A (a ⊗ₜ x) = a ⊗ₜ (f x) := rfl

lemma base_change_eq_ltensor :
  (f.base_change A : A ⊗ M → A ⊗ N) = f.ltensor A := rfl

@[simp] lemma base_change_add :
  (f + g).base_change A = f.base_change A + g.base_change A :=
by { ext, simp [base_change_eq_ltensor], }

@[simp] lemma base_change_zero : base_change A (0 : M →ₗ[R] N) = 0 :=
by { ext, simp [base_change_eq_ltensor], }

@[simp] lemma base_change_smul : (r • f).base_change A = r • (f.base_change A) :=
by { ext, simp [base_change_tmul], }

variables (R A M N)
/-- `base_change` as a linear map. -/
@[simps] def base_change_hom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N :=
{ to_fun := base_change A,
  map_add' := base_change_add,
  map_smul' := base_change_smul }

end semiring

section ring

variables {R A B M N : Type*} [comm_ring R]
variables [ring A] [algebra R A] [ring B] [algebra R B]
variables [add_comm_group M] [module R M] [add_comm_group N] [module R N]
variables (f g : M →ₗ[R] N)

@[simp] lemma base_change_sub :
  (f - g).base_change A = f.base_change A - g.base_change A :=
by { ext, simp [base_change_eq_ltensor], }

@[simp] lemma base_change_neg : (-f).base_change A = -(f.base_change A) :=
by { ext, simp [base_change_eq_ltensor], }

end ring

end linear_map

namespace algebra
namespace tensor_product

section semiring

variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mul_aux (a₁ : A) (b₁ : B) : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
tensor_product.map (linear_map.mul_left R a₁) (linear_map.mul_left R b₁)

@[simp]
lemma mul_aux_apply (a₁ a₂ : A) (b₁ b₂ : B) :
  (mul_aux a₁ b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
tensor_product.lift $ linear_map.mk₂ R mul_aux
  (λ x₁ x₂ y, tensor_product.ext' $ λ x' y',
    by simp only [mul_aux_apply, linear_map.add_apply, add_mul, add_tmul])
  (λ c x y, tensor_product.ext' $ λ x' y',
    by simp only [mul_aux_apply, linear_map.smul_apply, smul_tmul', smul_mul_assoc])
  (λ x y₁ y₂, tensor_product.ext' $ λ x' y',
    by simp only [mul_aux_apply, linear_map.add_apply, add_mul, tmul_add])
  (λ c x y, tensor_product.ext' $ λ x' y',
    by simp only [mul_aux_apply, linear_map.smul_apply, smul_tmul, smul_tmul', smul_mul_assoc])

@[simp]
lemma mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
  mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

lemma mul_assoc' (mul : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B))
  (h : ∀ (a₁ a₂ a₃ : A) (b₁ b₂ b₃ : B),
    mul (mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂)) (a₃ ⊗ₜ[R] b₃) =
      mul (a₁ ⊗ₜ[R] b₁) (mul (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃))) :
  ∀ (x y z : A ⊗[R] B), mul (mul x y) z = mul x (mul y z) :=
begin
  intros,
  apply tensor_product.induction_on x,
  { simp only [linear_map.map_zero, linear_map.zero_apply], },
  apply tensor_product.induction_on y,
  { simp only [linear_map.map_zero, forall_const, linear_map.zero_apply], },
  apply tensor_product.induction_on z,
  { simp only [linear_map.map_zero, forall_const], },
  { intros, simp only [h], },
  { intros, simp only [linear_map.map_add, *], },
  { intros, simp only [linear_map.map_add, *, linear_map.add_apply], },
  { intros, simp only [linear_map.map_add, *, linear_map.add_apply], },
end

lemma mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) :=
mul_assoc' mul (by { intros, simp only [mul_apply, mul_assoc], }) x y z

lemma one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x :=
begin
  apply tensor_product.induction_on x;
  simp {contextual := tt},
end

lemma mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x :=
begin
  apply tensor_product.induction_on x;
  simp {contextual := tt},
end

instance : has_one (A ⊗[R] B) :=
{ one := 1 ⊗ₜ 1 }

instance : add_monoid_with_one (A ⊗[R] B) := add_monoid_with_one.unary

instance : semiring (A ⊗[R] B) :=
{ zero := 0,
  add := (+),
  one := 1,
  mul := λ a b, mul a b,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  zero_mul := by simp,
  mul_zero := by simp,
  left_distrib := by simp,
  right_distrib := by simp,
  .. (by apply_instance : add_monoid_with_one (A ⊗[R] B)),
  .. (by apply_instance : add_comm_monoid (A ⊗[R] B)) }.

lemma one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) := rfl

@[simp]
lemma tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
  (a₁ ⊗ₜ[R] b₁) * (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

@[simp]
lemma tmul_pow (a : A) (b : B) (k : ℕ) :
  (a ⊗ₜ[R] b)^k = (a^k) ⊗ₜ[R] (b^k) :=
begin
  induction k with k ih,
  { simp [one_def], },
  { simp [pow_succ, ih], }
end


/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def include_left_ring_hom : A →+* A ⊗[R] B :=
{ to_fun := λ a, a ⊗ₜ 1,
  map_zero' := by simp,
  map_add' := by simp [add_tmul],
  map_one' := rfl,
  map_mul' := by simp }

variables {S : Type*} [comm_semiring S] [algebra R S] [algebra S A] [is_scalar_tower R S A]

instance left_algebra : algebra S (A ⊗[R] B) :=
{ commutes' := λ r x,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros a b, dsimp, rw [algebra.commutes, _root_.mul_one, _root_.one_mul], },
    { intros y y' h h', dsimp at h h' ⊢, simp only [mul_add, add_mul, h, h'], },
  end,
  smul_def' := λ r x,
  begin
    apply tensor_product.induction_on x,
    { simp [smul_zero], },
    { intros a b, dsimp, rw [tensor_product.smul_tmul', algebra.smul_def r a, _root_.one_mul] },
    { intros, dsimp, simp [smul_add, mul_add, *], },
  end,
  .. tensor_product.include_left_ring_hom.comp (algebra_map S A),
  .. (by apply_instance : module S (A ⊗[R] B)) }.

-- This is for the `undergrad.yaml` list.
/-- The tensor product of two `R`-algebras is an `R`-algebra. -/
instance : algebra R (A ⊗[R] B) := infer_instance

@[simp]
lemma algebra_map_apply (r : S) :
  (algebra_map S (A ⊗[R] B)) r = ((algebra_map S A) r) ⊗ₜ 1 := rfl

instance : is_scalar_tower R S (A ⊗[R] B) := ⟨λ a b c, by simp⟩

variables {C : Type v₃} [semiring C] [algebra R C]

@[ext]
theorem ext {g h : (A ⊗[R] B) →ₐ[R] C}
  (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
begin
  apply @alg_hom.to_linear_map_injective R (A ⊗[R] B) C _ _ _ _ _ _ _ _,
  ext,
  simp [H],
end

/-- The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def include_left : A →ₐ[R] A ⊗[R] B :=
{ commutes' := by simp,
  ..include_left_ring_hom }

@[simp]
lemma include_left_apply (a : A) : (include_left : A →ₐ[R] A ⊗[R] B) a = a ⊗ₜ 1 := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
def include_right : B →ₐ[R] A ⊗[R] B :=
{ to_fun := λ b, 1 ⊗ₜ b,
  map_zero' := by simp,
  map_add' := by simp [tmul_add],
  map_one' := rfl,
  map_mul' := by simp,
  commutes' := λ r,
  begin
    simp only [algebra_map_apply],
    transitivity r • ((1 : A) ⊗ₜ[R] (1 : B)),
    { rw [←tmul_smul, algebra.smul_def], simp, },
    { simp [algebra.smul_def], },
  end, }

@[simp]
lemma include_right_apply (b : B) : (include_right : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b := rfl

lemma include_left_comp_algebra_map {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] :
    (include_left.to_ring_hom.comp (algebra_map R S) : R →+* S ⊗[R] T) =
      include_right.to_ring_hom.comp (algebra_map R T) :=
by { ext, simp }

end semiring

section ring

variables {R : Type u} [comm_ring R]
variables {A : Type v₁} [ring A] [algebra R A]
variables {B : Type v₂} [ring B] [algebra R B]

instance : ring (A ⊗[R] B) :=
{ .. (by apply_instance : add_comm_group (A ⊗[R] B)),
  .. (by apply_instance : semiring (A ⊗[R] B)) }.

end ring

section comm_ring

variables {R : Type u} [comm_ring R]
variables {A : Type v₁} [comm_ring A] [algebra R A]
variables {B : Type v₂} [comm_ring B] [algebra R B]

instance : comm_ring (A ⊗[R] B) :=
{ mul_comm := λ x y,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros a₁ b₁,
      apply tensor_product.induction_on y,
      { simp, },
      { intros a₂ b₂,
        simp [mul_comm], },
      { intros a₂ b₂ ha hb,
        simp [mul_add, add_mul, ha, hb], }, },
    { intros x₁ x₂ h₁ h₂,
      simp [mul_add, add_mul, h₁, h₂], },
  end
  .. (by apply_instance : ring (A ⊗[R] B)) }.

section right_algebra

/-- `S ⊗[R] T` has a `T`-algebra structure. This is not a global instance or else the action of
`S` on `S ⊗[R] S` would be ambiguous. -/
@[reducible] def right_algebra : algebra B (A ⊗[R] B) :=
(algebra.tensor_product.include_right.to_ring_hom : B →+* A ⊗[R] B).to_algebra

local attribute [instance] tensor_product.right_algebra

instance right_is_scalar_tower : is_scalar_tower R B (A ⊗[R] B) :=
is_scalar_tower.of_algebra_map_eq (λ r, (algebra.tensor_product.include_right.commutes r).symm)

end right_algebra

end comm_ring

/--
Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [ring A] {B : Type v₂} [ring B] : ring (A ⊗[ℤ] B) :=
by apply_instance

/--
Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [comm_ring A] {B : Type v₂} [comm_ring B] : comm_ring (A ⊗[ℤ] B) :=
by apply_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/
section monoidal

section
variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]
variables {C : Type v₃} [semiring C] [algebra R C]
variables {D : Type v₄} [semiring D] [algebra R D]

/--
Build an algebra morphism from a linear map out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_hom_of_linear_map_tensor_product
  (f : A ⊗[R] B →ₗ[R] C)
  (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
  (w₂ : ∀ r, f ((algebra_map R A) r ⊗ₜ[R] 1) = (algebra_map R C) r):
  A ⊗[R] B →ₐ[R] C :=
{ map_one' := by rw [←(algebra_map R C).map_one, ←w₂, (algebra_map R A).map_one]; refl,
  map_zero' := by rw [linear_map.to_fun_eq_coe, map_zero],
  map_mul' := λ x y, by
  { rw linear_map.to_fun_eq_coe,
    apply tensor_product.induction_on x,
    { rw [zero_mul, map_zero, zero_mul] },
    { intros a₁ b₁,
      apply tensor_product.induction_on y,
      { rw [mul_zero, map_zero, mul_zero] },
      { intros a₂ b₂,
        rw [tmul_mul_tmul, w₁] },
      { intros x₁ x₂ h₁ h₂,
        rw [mul_add, map_add, map_add, mul_add, h₁, h₂] } },
    { intros x₁ x₂ h₁ h₂,
      rw [add_mul, map_add, map_add, add_mul, h₁, h₂] } },
  commutes' := λ r, by rw [linear_map.to_fun_eq_coe, algebra_map_apply, w₂],
  .. f }

@[simp]
lemma alg_hom_of_linear_map_tensor_product_apply (f w₁ w₂ x) :
  (alg_hom_of_linear_map_tensor_product f w₁ w₂ : A ⊗[R] B →ₐ[R] C) x = f x := rfl

/--
Build an algebra equivalence from a linear equivalence out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_equiv_of_linear_equiv_tensor_product
  (f : A ⊗[R] B ≃ₗ[R] C)
  (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
  (w₂ : ∀ r, f ((algebra_map R A) r ⊗ₜ[R] 1) = (algebra_map R C) r):
  A ⊗[R] B ≃ₐ[R] C :=
{ .. alg_hom_of_linear_map_tensor_product (f : A ⊗[R] B →ₗ[R] C) w₁ w₂,
  .. f }

@[simp]
lemma alg_equiv_of_linear_equiv_tensor_product_apply (f w₁ w₂ x) :
  (alg_equiv_of_linear_equiv_tensor_product f w₁ w₂ : A ⊗[R] B ≃ₐ[R] C) x = f x := rfl

/--
Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_equiv_of_linear_equiv_triple_tensor_product
  (f : ((A ⊗[R] B) ⊗[R] C) ≃ₗ[R] D)
  (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
    f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
  (w₂ : ∀ r, f (((algebra_map R A) r ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = (algebra_map R D) r) :
  (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
{ to_fun := f,
  map_mul' := λ x y,
  begin
    apply tensor_product.induction_on x,
    { simp only [map_zero, zero_mul] },
    { intros ab₁ c₁,
      apply tensor_product.induction_on y,
      { simp only [map_zero, mul_zero] },
      { intros ab₂ c₂,
        apply tensor_product.induction_on ab₁,
        { simp only [zero_tmul, map_zero, zero_mul] },
        { intros a₁ b₁,
          apply tensor_product.induction_on ab₂,
          { simp only [zero_tmul, map_zero, mul_zero] },
          { intros, simp only [tmul_mul_tmul, w₁] },
          { intros x₁ x₂ h₁ h₂,
            simp only [tmul_mul_tmul] at h₁ h₂,
            simp only [tmul_mul_tmul, mul_add, add_tmul, map_add, h₁, h₂] } },
        { intros x₁ x₂ h₁ h₂,
          simp only [tmul_mul_tmul] at h₁ h₂,
          simp only [tmul_mul_tmul, add_mul, add_tmul, map_add, h₁, h₂] } },
      { intros x₁ x₂ h₁ h₂,
        simp only [tmul_mul_tmul, map_add, mul_add, add_mul, h₁, h₂], }, },
    { intros x₁ x₂ h₁ h₂,
      simp only [tmul_mul_tmul, map_add, mul_add, add_mul, h₁, h₂], }
  end,
  commutes' := λ r, by simp [w₂],
  .. f }

@[simp]
lemma alg_equiv_of_linear_equiv_triple_tensor_product_apply (f w₁ w₂ x) :
  (alg_equiv_of_linear_equiv_triple_tensor_product f w₁ w₂ : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D) x = f x :=
rfl

end

variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]
variables {C : Type v₃} [semiring C] [algebra R C]
variables {D : Type v₄} [semiring D] [algebra R D]

section
variables (R A)
/--
The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def lid : R ⊗[R] A ≃ₐ[R] A :=
alg_equiv_of_linear_equiv_tensor_product (tensor_product.lid R A)
(by simp [mul_smul]) (by simp [algebra.smul_def])

@[simp] theorem lid_tmul (r : R) (a : A) :
  (tensor_product.lid R A : (R ⊗ A → A)) (r ⊗ₜ a) = r • a :=
by simp [tensor_product.lid]

/--
The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def rid : A ⊗[R] R ≃ₐ[R] A :=
alg_equiv_of_linear_equiv_tensor_product (tensor_product.rid R A)
(by simp [mul_smul]) (by simp [algebra.smul_def])

@[simp] theorem rid_tmul (r : R) (a : A) :
  (tensor_product.rid R A : (A ⊗ R → A)) (a ⊗ₜ r) = r • a :=
by simp [tensor_product.rid]

section
variables (R A B)

/--
The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
alg_equiv_of_linear_equiv_tensor_product (tensor_product.comm R A B)
(by simp)
(λ r, begin
  transitivity r • ((1 : B) ⊗ₜ[R] (1 : A)),
  { rw [←tmul_smul, algebra.smul_def], simp, },
  { simp [algebra.smul_def], },
end)

@[simp]
theorem comm_tmul (a : A) (b : B) :
  (tensor_product.comm R A B : (A ⊗[R] B → B ⊗[R] A)) (a ⊗ₜ b) = (b ⊗ₜ a) :=
by simp [tensor_product.comm]

lemma adjoin_tmul_eq_top : adjoin R {t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t} = ⊤ :=
top_le_iff.mp $ (top_le_iff.mpr $ span_tmul_eq_top R A B).trans (span_le_adjoin R _)

end

section
variables {R A B C}

lemma assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
  (tensor_product.assoc R A B C) (((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) ⊗ₜ[R] (c₁ * c₂)) =
    (tensor_product.assoc R A B C) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[R] c₁) *
      (tensor_product.assoc R A B C) ((a₂ ⊗ₜ[R] b₂) ⊗ₜ[R] c₂) :=
rfl

lemma assoc_aux_2 (r : R) :
  (tensor_product.assoc R A B C) (((algebra_map R A) r ⊗ₜ[R] 1) ⊗ₜ[R] 1) =
    (algebra_map R (A ⊗ (B ⊗ C))) r := rfl

variables (R A B C)

/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C)) :=
alg_equiv_of_linear_equiv_triple_tensor_product
  (tensor_product.assoc.{u v₁ v₂ v₃} R A B C : (A ⊗ B ⊗ C) ≃ₗ[R] (A ⊗ (B ⊗ C)))
  (@algebra.tensor_product.assoc_aux_1.{u v₁ v₂ v₃} R _ A _ _ B _ _ C _ _)
  (@algebra.tensor_product.assoc_aux_2.{u v₁ v₂ v₃} R _ A _ _ B _ _ C _ _)

variables {R A B C}

@[simp] theorem assoc_tmul (a : A) (b : B) (c : C) :
  ((tensor_product.assoc R A B C) :
  (A ⊗[R] B) ⊗[R] C → A ⊗[R] (B ⊗[R] C)) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
rfl

end

variables {R A B C D}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[R] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[R] B ⊗[R] D :=
alg_hom_of_linear_map_tensor_product
  (tensor_product.map f.to_linear_map g.to_linear_map)
  (by simp)
  (by simp [alg_hom.commutes])

@[simp] theorem map_tmul (f : A →ₐ[R] B) (g : C →ₐ[R] D) (a : A) (c : C) :
  map f g (a ⊗ₜ c) = f a ⊗ₜ g c :=
rfl

@[simp] lemma map_comp_include_left (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
  (map f g).comp include_left = include_left.comp f := alg_hom.ext $ by simp

@[simp] lemma map_comp_include_right (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
  (map f g).comp include_right = include_right.comp g := alg_hom.ext $ by simp

lemma map_range (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
  (map f g).range = (include_left.comp f).range ⊔ (include_right.comp g).range :=
begin
  apply le_antisymm,
  { rw [←map_top, ←adjoin_tmul_eq_top, ←adjoin_image, adjoin_le_iff],
    rintros _ ⟨_, ⟨a, b, rfl⟩, rfl⟩,
    rw [map_tmul, ←_root_.mul_one (f a), ←_root_.one_mul (g b), ←tmul_mul_tmul],
    exact mul_mem_sup (alg_hom.mem_range_self _ a) (alg_hom.mem_range_self _ b) },
  { rw [←map_comp_include_left f g, ←map_comp_include_right f g],
    exact sup_le (alg_hom.range_comp_le_range _ _) (alg_hom.range_comp_le_range _ _) },
end

/--
Construct an isomorphism between tensor products of R-algebras
from isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[R] B ⊗[R] D :=
alg_equiv.of_alg_hom (map f g) (map f.symm g.symm)
  (ext $ λ b d, by simp)
  (ext $ λ a c, by simp)

@[simp]
lemma congr_apply (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x) :
  congr f g x = (map (f : A →ₐ[R] B) (g : C →ₐ[R] D)) x := rfl

@[simp]
lemma congr_symm_apply (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x) :
  (congr f g).symm x = (map (f.symm : B →ₐ[R] A) (g.symm : D →ₐ[R] C)) x := rfl

end

end monoidal

section

variables {R A B S : Type*} [comm_semiring R] [semiring A] [semiring B] [comm_semiring S]
variables [algebra R A] [algebra R B] [algebra R S]
variables (f : A →ₐ[R] S) (g : B →ₐ[R] S)

variables (R)

/-- `linear_map.mul'` is an alg_hom on commutative rings. -/
def lmul' : S ⊗[R] S →ₐ[R] S :=
alg_hom_of_linear_map_tensor_product (linear_map.mul' R S)
  (λ a₁ a₂ b₁ b₂, by simp only [linear_map.mul'_apply, mul_mul_mul_comm])
  (λ r, by simp only [linear_map.mul'_apply, _root_.mul_one])

variables {R}

lemma lmul'_to_linear_map : (lmul' R : _ →ₐ[R] S).to_linear_map = linear_map.mul' R S := rfl

@[simp] lemma lmul'_apply_tmul (a b : S) : lmul' R (a ⊗ₜ[R] b) = a * b := rfl

@[simp]
lemma lmul'_comp_include_left : (lmul' R : _ →ₐ[R] S).comp include_left = alg_hom.id R S :=
alg_hom.ext $ _root_.mul_one

@[simp]
lemma lmul'_comp_include_right : (lmul' R : _ →ₐ[R] S).comp include_right = alg_hom.id R S :=
alg_hom.ext $ _root_.one_mul

/--
If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.
-/
def product_map : A ⊗[R] B →ₐ[R] S := (lmul' R).comp (tensor_product.map f g)

@[simp] lemma product_map_apply_tmul (a : A) (b : B) : product_map f g (a ⊗ₜ b) = f a * g b :=
by { unfold product_map lmul', simp }

lemma product_map_left_apply (a : A) :
  product_map f g ((include_left : A →ₐ[R] A ⊗ B) a) = f a := by simp

@[simp] lemma product_map_left : (product_map f g).comp include_left = f := alg_hom.ext $ by simp

lemma product_map_right_apply (b : B) : product_map f g (include_right b) = g b := by simp

@[simp] lemma product_map_right : (product_map f g).comp include_right = g := alg_hom.ext $ by simp

lemma product_map_range : (product_map f g).range = f.range ⊔ g.range :=
by rw [product_map, alg_hom.range_comp, map_range, map_sup, ←alg_hom.range_comp,
    ←alg_hom.range_comp, ←alg_hom.comp_assoc, ←alg_hom.comp_assoc, lmul'_comp_include_left,
    lmul'_comp_include_right, alg_hom.id_comp, alg_hom.id_comp]

end
section

variables {R A A' B S : Type*}
variables [comm_semiring R] [comm_semiring A] [semiring A'] [semiring B] [comm_semiring S]
variables [algebra R A] [algebra R A'] [algebra A A'] [is_scalar_tower R A A'] [algebra R B]
variables [algebra R S] [algebra A S] [is_scalar_tower R A S]

/-- If `A`, `B` are `R`-algebras, `A'` is an `A`-algebra, then the product map of `f : A' →ₐ[A] S`
and `g : B →ₐ[R] S` is an `A`-algebra homomorphism. -/
@[simps] def product_left_alg_hom (f : A' →ₐ[A] S) (g : B →ₐ[R] S) : A' ⊗[R] B →ₐ[A] S :=
{ commutes' := λ r, by { dsimp, simp },
  ..(product_map (f.restrict_scalars R) g).to_ring_hom }

end
section basis

variables {k : Type*} [comm_ring k] (R : Type*) [ring R] [algebra k R] {M : Type*}
  [add_comm_monoid M] [module k M] {ι : Type*} (b : basis ι k M)

/-- Given a `k`-algebra `R` and a `k`-basis of `M,` this is a `k`-linear isomorphism
`R ⊗[k] M ≃ (ι →₀ R)` (which is in fact `R`-linear). -/
noncomputable def basis_aux : R ⊗[k] M ≃ₗ[k] (ι →₀ R) :=
(_root_.tensor_product.congr (finsupp.linear_equiv.finsupp_unique k R punit).symm b.repr) ≪≫ₗ
  (finsupp_tensor_finsupp k R k punit ι).trans (finsupp.lcongr (equiv.unique_prod ι punit)
  (_root_.tensor_product.rid k R))

variables {R}

lemma basis_aux_tmul (r : R) (m : M) :
  basis_aux R b (r ⊗ₜ m) = r • (finsupp.map_range (algebra_map k R)
    (map_zero _) (b.repr m)) :=
begin
  ext,
  simp [basis_aux, ←algebra.commutes, algebra.smul_def],
end

lemma basis_aux_map_smul (r : R) (x : R ⊗[k] M) :
  basis_aux R b (r • x) = r • basis_aux R b x :=
tensor_product.induction_on x (by simp) (λ x y, by simp only [tensor_product.smul_tmul',
  basis_aux_tmul, smul_assoc]) (λ x y hx hy, by simp [hx, hy])

variables (R)

/-- Given a `k`-algebra `R`, this is the `R`-basis of `R ⊗[k] M` induced by a `k`-basis of `M`. -/
noncomputable def basis : basis ι R (R ⊗[k] M) :=
{ repr := { map_smul' := basis_aux_map_smul b, .. basis_aux R b } }

variables {R}

@[simp] lemma basis_repr_tmul (r : R) (m : M) :
  (basis R b).repr (r ⊗ₜ m) = r • (finsupp.map_range (algebra_map k R) (map_zero _) (b.repr m)) :=
basis_aux_tmul _ _ _

@[simp] lemma basis_repr_symm_apply (r : R) (i : ι) :
  (basis R b).repr.symm (finsupp.single i r) = r ⊗ₜ b.repr.symm (finsupp.single i 1) :=
by simp [basis, equiv.unique_prod_symm_apply, basis_aux]

end basis
end tensor_product
end algebra

namespace module

variables {R M N : Type*} [comm_semiring R]
variables [add_comm_monoid M] [add_comm_monoid N]
variables [module R M] [module R N]

/-- The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` to
the `tensor_product.map f g`, the tensor product of the two maps. -/
def End_tensor_End_alg_hom : (End R M) ⊗[R] (End R N) →ₐ[R] End R (M ⊗[R] N) :=
begin
  refine algebra.tensor_product.alg_hom_of_linear_map_tensor_product
    (hom_tensor_hom_map R M N M N) _ _,
  { intros f₁ f₂ g₁ g₂,
    simp only [hom_tensor_hom_map_apply, tensor_product.map_mul] },
  { intro r,
    simp only [hom_tensor_hom_map_apply],
    ext m n, simp [smul_tmul] }
end

lemma End_tensor_End_alg_hom_apply (f : End R M) (g : End R N) :
  End_tensor_End_alg_hom (f ⊗ₜ[R] g) = tensor_product.map f g :=
by simp only [End_tensor_End_alg_hom,
  algebra.tensor_product.alg_hom_of_linear_map_tensor_product_apply, hom_tensor_hom_map_apply]

end module

lemma subalgebra.finite_dimensional_sup {K L : Type*} [field K] [comm_ring L] [algebra K L]
  (E1 E2 : subalgebra K L) [finite_dimensional K E1] [finite_dimensional K E2] :
  finite_dimensional K ↥(E1 ⊔ E2) :=
begin
  rw [←E1.range_val, ←E2.range_val, ←algebra.tensor_product.product_map_range],
  exact (algebra.tensor_product.product_map E1.val E2.val).to_linear_map.finite_dimensional_range,
end

namespace tensor_product.algebra

variables {R A B M : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables [semiring A] [semiring B] [module A M] [module B M]
variables [algebra R A] [algebra R B]
variables [is_scalar_tower R A M] [is_scalar_tower R B M]

/-- An auxiliary definition, used for constructing the `module (A ⊗[R] B) M` in
`tensor_product.algebra.module` below. -/
def module_aux : A ⊗[R] B →ₗ[R] M →ₗ[R] M :=
tensor_product.lift
{ to_fun := λ a, a • (algebra.lsmul R M : B →ₐ[R] module.End R M).to_linear_map,
  map_add' := λ r t, by { ext, simp only [add_smul, linear_map.add_apply] },
  map_smul' := λ n r, by { ext, simp only [ring_hom.id_apply, linear_map.smul_apply, smul_assoc] } }

lemma module_aux_apply (a : A) (b : B) (m : M) :
  module_aux (a ⊗ₜ[R] b) m = a • b • m := rfl

variables [smul_comm_class A B M]

/-- If `M` is a representation of two different `R`-algebras `A` and `B` whose actions commute,
then it is a representation the `R`-algebra `A ⊗[R] B`.

An important example arises from a semiring `S`; allowing `S` to act on itself via left and right
multiplication, the roles of `R`, `A`, `B`, `M` are played by `ℕ`, `S`, `Sᵐᵒᵖ`, `S`. This example
is important because a submodule of `S` as a `module` over `S ⊗[ℕ] Sᵐᵒᵖ` is a two-sided ideal.

NB: This is not an instance because in the case `B = A` and `M = A ⊗[R] A` we would have a diamond
of `smul` actions. Furthermore, this would not be a mere definitional diamond but a true
mathematical diamond in which `A ⊗[R] A` had two distinct scalar actions on itself: one from its
multiplication, and one from this would-be instance. Arguably we could live with this but in any
case the real fix is to address the ambiguity in notation, probably along the lines outlined here:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234773.20base.20change/near/240929258
-/
protected def module : module (A ⊗[R] B) M :=
{ smul := λ x m, module_aux x m,
  zero_smul := λ m, by simp only [map_zero, linear_map.zero_apply],
  smul_zero := λ x, by simp only [map_zero],
  smul_add := λ x m₁ m₂, by simp only [map_add],
  add_smul := λ x y m, by simp only [map_add, linear_map.add_apply],
  one_smul := λ m, by simp only [module_aux_apply, algebra.tensor_product.one_def, one_smul],
  mul_smul := λ x y m,
  begin
    apply tensor_product.induction_on x;
    apply tensor_product.induction_on y,
    { simp only [mul_zero, map_zero, linear_map.zero_apply], },
    { intros a b, simp only [zero_mul, map_zero, linear_map.zero_apply], },
    { intros z w hz hw, simp only [zero_mul, map_zero, linear_map.zero_apply], },
    { intros a b, simp only [mul_zero, map_zero, linear_map.zero_apply], },
    { intros a₁ b₁ a₂ b₂,
      simp only [module_aux_apply, mul_smul, smul_comm a₁ b₂, algebra.tensor_product.tmul_mul_tmul,
        linear_map.mul_apply], },
    { intros z w hz hw a b,
      simp only at hz hw,
      simp only [mul_add, hz, hw, map_add, linear_map.add_apply], },
    { intros z w hz hw, simp only [mul_zero, map_zero, linear_map.zero_apply], },
    { intros a b z w hz hw,
      simp only at hz hw,
      simp only [map_add, add_mul, linear_map.add_apply, hz, hw], },
    { intros u v hu hv z w hz hw,
      simp only at hz hw,
      simp only [add_mul, hz, hw, map_add, linear_map.add_apply], },
  end }

local attribute [instance] tensor_product.algebra.module

lemma smul_def (a : A) (b : B) (m : M) : (a ⊗ₜ[R] b) • m = a • b • m := rfl

end tensor_product.algebra

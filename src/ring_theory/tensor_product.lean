/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/

import linear_algebra.tensor_product_basis
import ring_theory.adjoin.basic

/-!
# The tensor product of R-algebras

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
{ map_smul' := λ c x, linear_map.ext $ λ y, f.map_smul c (x ⊗ₜ y),
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
lift.tmul' x y

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
    show (f.ltensor A) (rtensor M (algebra.lmul R A a) x) =
      (rtensor N ((algebra.lmul R A) a)) ((ltensor A f) x),
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
tensor_product.map (lmul_left R a₁) (lmul_left R b₁)

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

instance : semiring (A ⊗[R] B) :=
{ zero := 0,
  add := (+),
  one := 1 ⊗ₜ 1,
  mul := λ a b, mul a b,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  zero_mul := by simp,
  mul_zero := by simp,
  left_distrib := by simp,
  right_distrib := by simp,
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


/--
The algebra map `R →+* (A ⊗[R] B)` giving `A ⊗[R] B` the structure of an `R`-algebra.
-/
def tensor_algebra_map : R →+* (A ⊗[R] B) :=
{ to_fun := λ r, algebra_map R A r ⊗ₜ[R] 1,
  map_one' := by { simp, refl },
  map_mul' := by simp,
  map_zero' := by simp [zero_tmul],
  map_add' := by simp [add_tmul], }

instance : algebra R (A ⊗[R] B) :=
{ commutes' := λ r x,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros a b, simp [tensor_algebra_map, algebra.commutes], },
    { intros y y' h h', simp at h h', simp [mul_add, add_mul, h, h'], },
  end,
  smul_def' := λ r x,
  begin
    apply tensor_product.induction_on x,
    { simp [smul_zero], },
    { intros a b,
      rw [tensor_algebra_map, ←tmul_smul, ←smul_tmul, algebra.smul_def r a],
      simp, },
    { intros, dsimp, simp [smul_add, mul_add, *], },
  end,
  .. tensor_algebra_map,
  .. (by apply_instance : module R (A ⊗[R] B)) }.

@[simp]
lemma algebra_map_apply (r : R) :
  (algebra_map R (A ⊗[R] B)) r = ((algebra_map R A) r) ⊗ₜ[R] 1 := rfl

variables {C : Type v₃} [semiring C] [algebra R C]

@[ext]
theorem ext {g h : (A ⊗[R] B) →ₐ[R] C}
  (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
begin
  apply @alg_hom.to_linear_map_injective R (A ⊗[R] B) C _ _ _ _ _ _ _ _,
  ext,
  simp [H],
end

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def include_left : A →ₐ[R] A ⊗[R] B :=
{ to_fun := λ a, a ⊗ₜ 1,
  map_zero' := by simp,
  map_add' := by simp [add_tmul],
  map_one' := rfl,
  map_mul' := by simp,
  commutes' := by simp, }

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

-- variables (R A B C)

-- -- local attribute [elab_simple] alg_equiv_of_linear_equiv_triple_tensor_product

-- /-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
-- -- FIXME This is _really_ slow to compile. :-(
-- protected def assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C)) :=
-- alg_equiv_of_linear_equiv_triple_tensor_product
--   (tensor_product.assoc R A B C)
--   assoc_aux_1 assoc_aux_2

-- variables {R A B C}

-- @[simp] theorem assoc_tmul (a : A) (b : B) (c : C) :
--   ((tensor_product.assoc R A B C) :
--   (A ⊗[R] B) ⊗[R] C → A ⊗[R] (B ⊗[R] C)) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
-- rfl

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

/-- `algebra.lmul'` is an alg_hom on commutative rings. -/
def lmul' : S ⊗[R] S →ₐ[R] S :=
alg_hom_of_linear_map_tensor_product (algebra.lmul' R)
  (λ a₁ a₂ b₁ b₂, by simp only [algebra.lmul'_apply, mul_mul_mul_comm])
  (λ r, by simp only [algebra.lmul'_apply, _root_.mul_one])

variables {R}

lemma lmul'_to_linear_map : (lmul' R : _ →ₐ[R] S).to_linear_map = algebra.lmul' R := rfl

@[simp] lemma lmul'_apply_tmul (a b : S) : lmul' R (a ⊗ₜ[R] b) = a * b := lmul'_apply

@[simp]
lemma lmul'_comp_include_left : (lmul' R : _ →ₐ[R] S).comp include_left = alg_hom.id R S :=
alg_hom.ext $ λ _, (lmul'_apply_tmul _ _).trans (_root_.mul_one _)

@[simp]
lemma lmul'_comp_include_right : (lmul' R : _ →ₐ[R] S).comp include_right = alg_hom.id R S :=
alg_hom.ext $ λ _, (lmul'_apply_tmul _ _).trans (_root_.one_mul _)

/--
If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.
-/
def product_map : A ⊗[R] B →ₐ[R] S := (lmul' R).comp (tensor_product.map f g)

@[simp] lemma product_map_apply_tmul (a : A) (b : B) : product_map f g (a ⊗ₜ b) = f a * g b :=
by { unfold product_map lmul', simp }

lemma product_map_left_apply (a : A) : product_map f g (include_left a) = f a := by simp

@[simp] lemma product_map_left : (product_map f g).comp include_left = f := alg_hom.ext $ by simp

lemma product_map_right_apply (b : B) : product_map f g (include_right b) = g b := by simp

@[simp] lemma product_map_right : (product_map f g).comp include_right = g := alg_hom.ext $ by simp

lemma product_map_range : (product_map f g).range = f.range ⊔ g.range :=
by rw [product_map, alg_hom.range_comp, map_range, map_sup, ←alg_hom.range_comp,
    ←alg_hom.range_comp, ←alg_hom.comp_assoc, ←alg_hom.comp_assoc, lmul'_comp_include_left,
    lmul'_comp_include_right, alg_hom.id_comp, alg_hom.id_comp]

end
end tensor_product
end algebra

lemma subalgebra.finite_dimensional_sup {K L : Type*} [field K] [comm_ring L] [algebra K L]
  (E1 E2 : subalgebra K L) [finite_dimensional K E1] [finite_dimensional K E2] :
  finite_dimensional K ↥(E1 ⊔ E2) :=
begin
  rw [←E1.range_val, ←E2.range_val, ←algebra.tensor_product.product_map_range],
  exact (algebra.tensor_product.product_map E1.val E2.val).to_linear_map.finite_dimensional_range,
end

section is_tensor_product

variables {R : Type*} [comm_ring R]
variables {M₁ M₂ M M' : Type*}
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M] [add_comm_monoid M']
variables [module R M₁] [module R M₂] [module R M] [module R M']
variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)
variables {N₁ N₂ N : Type*} [add_comm_monoid N₁] [add_comm_monoid N₂] [add_comm_monoid N]
variables [module R N₁] [module R N₂] [module R N]
variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

/--
Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `is_tensor_product f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def is_tensor_product : Prop := function.bijective (tensor_product.lift f)

variables (R M N) {f}

lemma tensor_product.is_tensor_product : is_tensor_product (tensor_product.mk R M N) :=
begin
  delta is_tensor_product,
  convert_to function.bijective linear_map.id using 2,
  { apply tensor_product.ext', simp },
  { exact function.bijective_id }
end

variables {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps apply] noncomputable
def is_tensor_product.equiv (h : is_tensor_product f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
linear_equiv.of_bijective _ h.1 h.2

@[simp] lemma is_tensor_product.equiv_to_linear_map (h : is_tensor_product f) :
  h.equiv.to_linear_map = tensor_product.lift f := rfl

@[simp] lemma is_tensor_product.equiv_symm_apply (h : is_tensor_product f) (x₁ : M₁) (x₂ : M₂) :
  h.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ :=
begin
  apply h.equiv.injective,
  refine (h.equiv.apply_symm_apply _).trans _,
  simp
end

/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
noncomputable
def is_tensor_product.lift (h : is_tensor_product f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') : M →ₗ[R] M' :=
(tensor_product.lift f').comp h.equiv.symm.to_linear_map

lemma is_tensor_product.lift_eq (h : is_tensor_product f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M')
  (x₁ : M₁) (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ :=
begin
  delta is_tensor_product.lift,
  simp,
end

/-- The tensor product of a pair of linear maps between modules. -/
noncomputable
def is_tensor_product.map (hf : is_tensor_product f) (hg : is_tensor_product g)
  (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
hg.equiv.to_linear_map.comp ((tensor_product.map i₁ i₂).comp hf.equiv.symm.to_linear_map)

lemma is_tensor_product.map_eq (hf : is_tensor_product f) (hg : is_tensor_product g)
  (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) :
    hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) :=
begin
  delta is_tensor_product.map,
  simp
end

lemma is_tensor_product.induction_on (h : is_tensor_product f) {C : M → Prop}
  (x : M)
  (h0 : C 0)
  (htmul : ∀ x₁ x₂, C (f x₁ x₂))
  (hadd : ∀ x₁ x₂, C x₁ → C x₂ → C (x₁ + x₂)) : C x :=
begin
  rw ← h.equiv.right_inv x,
  generalize : h.equiv.inv_fun x = y,
  change C (tensor_product.lift f y),
  induction y using tensor_product.induction_on,
  { rwa map_zero },
  { rw tensor_product.lift.tmul, apply htmul },
  { rw map_add, apply hadd; assumption }
end

end is_tensor_product

section is_base_change

variables (R S M N : Type*) [add_comm_monoid M] [add_comm_monoid N] [comm_ring R]
variables [comm_ring S] [algebra R S] [module R M] [module R N] [module S N] [is_scalar_tower R S N]
variables (f : M →ₗ[R] N)

def linear_map.restrict_scalars_map : (N →ₗ[S] N) →ₗ[R] (N →ₗ[R] N) :=
{ to_fun := linear_map.restrict_scalars R,
  map_add' := λ f g, rfl,
  map_smul' := λ r f, rfl }

@[simps]
def algebra_alg_hom (R S : Type*) [comm_semiring R] [semiring S] [algebra R S] : R →ₐ[R] S :=
{ commutes' := λ r, rfl, ..(algebra_map R S) }

include f

variables {R M N}

example : module S (M →ₗ[R] N) := infer_instance

/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
def is_base_change : Prop := is_tensor_product
(((algebra_alg_hom S $ module.End S (M →ₗ[R] N)).to_linear_map.flip f).restrict_scalars R)

variables {S f} (h : is_base_change S f)
variables {P Q : Type*} [add_comm_monoid P] [module R P]
variables[add_comm_monoid Q] [module R Q] [module S Q] [is_scalar_tower R S Q]

/-- Suppoe `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors thorugh `f`. -/
noncomputable
def is_base_change.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
{ map_smul' := λ r x, begin
    let F := ((algebra_alg_hom S $ module.End S (M →ₗ[R] Q))
      .to_linear_map.flip g).restrict_scalars R,
    have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F,
    change h.lift F (r • x) = r • h.lift F x,
    apply h.induction_on x,
    { rw [smul_zero, map_zero, smul_zero] },
    { intros s m,
      change h.lift F (r • s • f m) = r • h.lift F (s • f m),
      rw [← mul_smul, hF, hF, mul_smul] },
    { intros x₁ x₂ e₁ e₂, rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }
  end,
  ..(h.lift (((algebra_alg_hom S $ module.End S (M →ₗ[R] Q))
    .to_linear_map.flip g).restrict_scalars R)) }

lemma is_base_change.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x :=
begin
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _,
  convert hF 1 x; rw one_smul,
end

lemma is_base_change.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrict_scalars R).comp f = g :=
linear_map.ext (h.lift_eq g)

variables (R M N S)

omit f

lemma tensor_product.is_base_change : is_base_change S (tensor_product.mk R S M 1) :=
begin
  delta is_base_change,
  convert tensor_product.is_tensor_product R S M using 1,
  ext s x,
  change s • 1 ⊗ₜ x = s ⊗ₜ x,
  rw tensor_product.smul_tmul',
  congr' 1,
  exact mul_one _,
end

variables {R M N S}

/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable
def is_base_change.equiv : S ⊗[R] M ≃ₗ[R] N := h.equiv

lemma is_base_change.equiv_tmul (s : S) (m : M) : h.equiv (s ⊗ₜ m) = s • (f m) :=
tensor_product.lift.tmul s m

lemma is_base_change.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 ⊗ₜ m :=
by rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]

end is_base_change

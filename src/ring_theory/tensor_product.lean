/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import linear_algebra.tensor_product
import ring_theory.algebra
import tactic

universes u v₁ v₂


/-!
The tensor product of R-algebras.
-/

namespace tensor_product.algebra

open_locale tensor_product
open tensor_product

section ring

variables {R : Type u} [comm_ring R]
variables {A : Type v₁} [ring A] [algebra R A]
variables {B : Type v₂} [ring B] [algebra R B]

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mul_aux (a₁ : A) (b₁ : B) : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
begin
  -- Why doesn't `apply tensor_product.lift` work?
  apply @tensor_product.lift R _ A B (A ⊗[R] B) _ _ _ _ _ _ _,
  fsplit,
  intro a₂,
  fsplit,
  intro b₂,
  exact (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂),
  { intros b₂ b₂',
    simp [mul_add, tmul_add], },
  { intros c b₂,
    simp [mul_smul, tmul_smul], },
  { intros a₂ a₂', ext b₂,
    simp [mul_add, add_tmul], },
  { intros c a₂, ext b₂,
    simp [mul_smul, smul_tmul], }
end

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
begin
  apply @tensor_product.lift R _ A B ((A ⊗[R] B) →ₗ[R] (A ⊗[R] B)) _ _ _ _ _ _ _,
  fsplit,
  intro a₁,
  fsplit,
  intro b₁,
  exact mul_aux a₁ b₁,
  { intros b₁ b₁',
    -- Why doesn't just `apply tensor_product.ext`, or indeed `ext` work?!
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp [add_mul, tmul_add], },
  { intros c b₁,
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp, },
  { intros a₁ a₁', ext1 b₁,
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp [add_mul, add_tmul], },
  { intros c a₁, ext1 b₁,
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp [smul_tmul], },
end

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
    apply tensor_product.induction_on A B x,
    { simp, },
    apply tensor_product.induction_on A B y,
    { simp, },
    apply tensor_product.induction_on A B z,
    { simp, },
    { intros, simp [h], },
    { intros, simp [linear_map.map_add, *], },
    { intros, simp [linear_map.map_add, *], },
    { intros, simp [linear_map.map_add, *], },
end

lemma mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) :=
mul_assoc' mul (by { intros, simp only [mul_apply, mul_assoc], }) x y z

lemma one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x :=
begin
  apply tensor_product.induction_on A B x;
  simp {contextual := tt},
end

lemma mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x :=
begin
  apply tensor_product.induction_on A B x;
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
  .. (by apply_instance : add_comm_group (A ⊗[R] B)) }.

instance : ring (A ⊗[R] B) :=
{ .. (by apply_instance : add_comm_group (A ⊗[R] B)),
  .. (by apply_instance : semiring (A ⊗[R] B)) }.

@[simp]
lemma mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
  (a₁ ⊗ₜ[R] b₁) * (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

/--
The algebra map `R →+* (A ⊗[R] B)` giving `A ⊗[R] B` the structure of an `R`-algebra.
-/
def algebra_map : R →+* (A ⊗[R] B) :=
{ to_fun := λ r, algebra_map R A r ⊗ₜ[R] 1,
  map_one' := by { simp, refl },
  map_mul' := by simp,
  map_zero' := by simp [zero_tmul],
  map_add' := by simp [add_tmul], }

instance : algebra R (A ⊗[R] B) :=
{ commutes' := λ r x,
  begin
    apply tensor_product.induction_on A B x,
    { simp, },
    { intros a b, simp [algebra_map, algebra.commutes], },
    { intros, simp [mul_add, add_mul, *], },
  end,
  smul_def' := λ r x,
  begin
    apply tensor_product.induction_on A B x,
    { simp, },
    { intros a b,
      rw [algebra_map, ←tmul_smul, ←smul_tmul, algebra.smul_def r a],
      simp, },
    { intros, dsimp, simp [smul_add, mul_add, *], },
  end,
  .. algebra_map,
  .. (by apply_instance : ring (A ⊗[R] B)) }.

end ring

section comm_ring

variables {R : Type u} [comm_ring R]
variables {A : Type v₁} [comm_ring A] [algebra R A]
variables {B : Type v₂} [comm_ring B] [algebra R B]

instance : comm_ring (A ⊗[R] B) :=
{ mul_comm := λ x y,
  begin
    apply tensor_product.induction_on A B x,
    { simp, },
    { intros a₁ b₁,
      apply tensor_product.induction_on A B y,
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
Verify that typeclass search finds the ring structure on `ring (A ⊗[ℤ] B)`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [ring A] {B : Type v₂} [ring B] : ring (A ⊗[ℤ] B) :=
by apply_instance

/--
Verify that typeclass search finds the comm_ring structure on `ring (A ⊗[ℤ] B)`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [comm_ring A] {B : Type v₂} [comm_ring B] : comm_ring (A ⊗[ℤ] B) :=
by apply_instance

end tensor_product.algebra

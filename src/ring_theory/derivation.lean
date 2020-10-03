/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import algebra.lie.basic
import ring_theory.algebra_tower

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Notation

The notation `⁅D1, D2⁆` is used for the commutator of two derivations.

TODO: this file is just a stub to go on with some PRs in the geometry section. It only
implements the definition of derivations in commutative algebra. This will soon change: as soon
as bimodules will be there in mathlib I will change this file to take into account the
non-commutative case. Any development on the theory of derivations is discouraged until the
definitive definition of derivation will be implemented.
-/

open algebra ring_hom

/-- `D : derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality.
TODO: update this when bimodules are defined. -/
@[protect_proj]
structure derivation (R : Type*) (A : Type*) [comm_semiring R] [comm_semiring A]
  [algebra R A] (M : Type*) [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M]
  [is_scalar_tower R A M]
  extends A →ₗ[R] M :=
(leibniz' (a b : A) : to_fun (a * b) = a • to_fun b + b • to_fun a)

namespace derivation

section

variables {R : Type*} [comm_semiring R]
variables {A : Type*} [comm_semiring A] [algebra R A]
variables {M : Type*} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M]
variables [is_scalar_tower R A M]
variables (D : derivation R A M) {D1 D2 : derivation R A M} (r : R) (a b : A)

instance : has_coe_to_fun (derivation R A M) := ⟨_, λ D, D.to_linear_map.to_fun⟩

instance has_coe_to_linear_map : has_coe (derivation R A M) (A →ₗ[R] M) :=
⟨λ D, D.to_linear_map⟩

@[simp] lemma to_fun_eq_coe : D.to_fun = ⇑D := rfl

@[simp, norm_cast]
lemma coe_fn_coe (f : derivation R A M) :
  ⇑(f : A →ₗ[R] M) = f := rfl

lemma coe_injective (H : ⇑D1 = D2) : D1 = D2 :=
by { cases D1, cases D2, congr', exact linear_map.coe_inj H }

@[ext] theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
coe_injective $ funext H

@[simp] lemma map_add : D (a + b) = D a + D b := is_add_hom.map_add D a b
@[simp] lemma map_zero : D 0 = 0 := is_add_monoid_hom.map_zero D
@[simp] lemma map_smul : D (r • a) = r • D a := linear_map.map_smul D r a
@[simp] lemma leibniz : D (a * b) = a • D b + b • D a := D.leibniz' _ _

@[simp] lemma map_one_eq_zero : D 1 = 0 :=
begin
  have h : D 1 = D (1 * 1) := by rw mul_one,
  rw [leibniz D 1 1, one_smul] at h,
  exact eq_zero_of_left_cancel_add_self h,
end

@[simp] lemma map_algebra_map : D (algebra_map R A r) = 0 :=
by rw [←mul_one r, ring_hom.map_mul, map_one, ←smul_def, map_smul, map_one_eq_zero, smul_zero]

instance : has_zero (derivation R A M) :=
⟨⟨(0 : A →ₗ[R] M), λ a b, by simp only [add_zero, linear_map.zero_apply,
                                        linear_map.to_fun_eq_coe, smul_zero]⟩⟩

instance : inhabited (derivation R A M) := ⟨0⟩

instance : add_comm_monoid (derivation R A M) :=
{ add := λ D1 D2, ⟨D1 + D2, λ a b, by { simp only [leibniz, linear_map.add_apply,
    linear_map.to_fun_eq_coe, coe_fn_coe, smul_add], cc }⟩,
  add_assoc := λ D E F, ext $ λ a, add_assoc _ _ _,
  zero_add := λ D, ext $ λ a, zero_add _,
  add_zero := λ D, ext $ λ a, add_zero _,
  add_comm := λ D E, ext $ λ a, add_comm _ _,
  ..derivation.has_zero }

@[simp] lemma add_apply : (D1 + D2) a = D1 a + D2 a := rfl

@[priority 100]
instance derivation.Rsemimodule : semimodule R (derivation R A M) :=
{ smul := λ r D, ⟨r • D, λ a b, by simp only [linear_map.smul_apply, leibniz,
    linear_map.to_fun_eq_coe, smul_algebra_smul_comm, coe_fn_coe, smul_add, add_comm],⟩,
  mul_smul := λ a1 a2 D, ext $ λ b, mul_smul _ _ _,
  one_smul := λ D, ext $ λ b, one_smul _ _,
  smul_add := λ a D1 D2, ext $ λ b, smul_add _ _ _,
  smul_zero := λ a, ext $ λ b, smul_zero _,
  add_smul := λ a1 a2 D, ext $ λ b, add_smul _ _ _,
  zero_smul := λ D, ext $ λ b, zero_smul _ _ }

@[simp] lemma smul_to_linear_map_coe : ↑(r • D) = (r • D : A →ₗ[R] M) := rfl
@[simp] lemma Rsmul_apply : (r • D) a = r • D a := rfl

instance : semimodule A (derivation R A M) :=
{ smul := λ a D, ⟨⟨λ b, a • D b,
    λ a1 a2, by rw [D.map_add, smul_add],
    λ a1 a2, by rw [D.map_smul, smul_algebra_smul_comm]⟩,
    λ b c, by { dsimp, simp only [smul_add, leibniz, smul_comm, add_comm] }⟩,
  mul_smul := λ a1 a2 D, ext $ λ b, mul_smul _ _ _,
  one_smul := λ D, ext $ λ b, one_smul A _,
  smul_add := λ a D1 D2, ext $ λ b, smul_add _ _ _,
  smul_zero := λ a, ext $ λ b, smul_zero _,
  add_smul := λ a1 a2 D, ext $ λ b, add_smul _ _ _,
  zero_smul := λ D, ext $ λ b, zero_smul A _ }

@[simp] lemma smul_apply : (a • D) b = a • D b := rfl

instance : is_scalar_tower R A (derivation R A M) :=
⟨λ x y z, ext (λ a, smul_assoc _ _ _)⟩

end

section

variables {R : Type*} [comm_ring R]
variables {A : Type*} [comm_ring A] [algebra R A]

section

variables {M : Type*} [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M]
variables (D : derivation R A M) {D1 D2 : derivation R A M} (r : R) (a b : A)

@[simp] lemma map_neg : D (-a) = -D a := linear_map.map_neg D a
@[simp] lemma map_sub : D (a - b) = D a - D b := linear_map.map_sub D a b

instance : add_comm_group (derivation R A M) :=
{ neg := λ D, ⟨-D, λ a b, by simp only [linear_map.neg_apply, smul_neg, neg_add_rev, leibniz,
    linear_map.to_fun_eq_coe, coe_fn_coe, add_comm]⟩,
  add_left_neg := λ D, ext $ λ a, add_left_neg _,
  ..derivation.add_comm_monoid }

end

section lie_structures

/-! # Lie structures -/

variables (D : derivation R A A) {D1 D2 : derivation R A A} (r : R) (a b : A)

open ring_commutator

/-- The commutator of derivations is again a derivation. -/
def commutator (D1 D2 : derivation R A A) : derivation R A A :=
⟨⁅D1, D2⁆, λ a b, by {simp only [commutator, map_add, id.smul_eq_mul, linear_map.mul_app,
  leibniz, linear_map.to_fun_eq_coe, coe_fn_coe, linear_map.sub_apply], ring }⟩

instance : has_bracket (derivation R A A) := ⟨derivation.commutator⟩

@[simp] lemma commutator_coe_linear_map : ↑⁅D1, D2⁆ = (⁅D1, D2⁆ : A →ₗ[R] A) := rfl

lemma commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) := rfl

instance : lie_ring (derivation R A A) :=
{ add_lie := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_add], ring },
  lie_add := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_add], ring },
  lie_self := λ d, by { ext a, simp only [commutator_apply, add_apply, map_add], ring },
  jacobi := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_sub], ring } }

instance : lie_algebra R (derivation R A A) :=
{ lie_smul := λ r d e, by { ext a, simp only [commutator_apply, map_smul, smul_sub, Rsmul_apply]},
  ..derivation.Rsemimodule }

end lie_structures

end

end derivation

section comp_der

namespace linear_map

variables {R : Type*} [comm_semiring R]
variables {A : Type*} [comm_semiring A] [algebra R A]
variables {M : Type*} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M]
variables {N : Type*} [add_cancel_comm_monoid N] [semimodule A N] [semimodule R N]
variables [is_scalar_tower R A M] [is_scalar_tower R A N]

/-- The composition of a linear map and a derivation is a derivation. -/
def comp_der (f : M →ₗ[A] N) (D : derivation R A M) : derivation R A N :=
{ to_fun := λ a, f (D a),
  map_add' := λ a1 a2, by rw [D.map_add, f.map_add],
  map_smul' := λ r a, by rw [derivation.map_smul, map_smul_eq_smul_map],
  leibniz' := λ a b, by simp only [derivation.leibniz, linear_map.map_smul, linear_map.map_add, add_comm] }

@[simp] lemma comp_der_apply (f : M →ₗ[A] N) (D : derivation R A M) (a : A) :
  f.comp_der D a = f (D a) := rfl

end linear_map

end comp_der

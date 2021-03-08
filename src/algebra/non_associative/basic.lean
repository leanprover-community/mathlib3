/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.basic

/-!
# Non-associative, non-unital algebras

This files defines non-associative, non-unital algebras together with their morphisms and basic
lemmas to make them usable.

## Main definitions

  * `na_semiring`
  * `na_algebra`
  * `na_algebra_hom`

## Tags

non-associative, non-unital, algebra
-/

universes u₁ u₂ u₃ u₄

variables (R : Type u₁) (A : Type u₂) (B : Type u₃) (C : Type u₄) [semiring R]

set_option old_structure_cmd true

/-- A not-necessarily-unital, not-necessarily-associative semiring, or "non-associative ring" for
short. -/
class na_semiring extends add_comm_monoid A, distrib A, mul_zero_class A

-- https://github.com/leanprover-community/lean/issues/285
set_option old_structure_cmd false

/-- A not-necessarily-unital, not-necessarily-associative algebra, or "non-associative algebra" for
short. -/
@[protect_proj]
class na_algebra [na_semiring A] extends semimodule R A :=
(smul_mul_assoc' : ∀ (t : R) (a b : A), (t • a) * b = t • (a * b))
(mul_smul_comm' : ∀ (t : R) (a b : A), a * (t • b) = t • (a * b))

@[priority 200] -- see Note [lower instance priority]
instance semiring.to_na_semiring [semiring A] : na_semiring A := { ..(infer_instance : semiring A) }

@[priority 200] -- see Note [lower instance priority]
instance algebra.to_na_algebra (R : Type u₁) [comm_semiring R] [semiring A] [algebra R A] :
  na_algebra R A :=
{ smul_mul_assoc' := algebra.smul_mul_assoc,
  mul_smul_comm'  := algebra.mul_smul_comm,
  ..algebra.to_semimodule }

namespace na_algebra

variables {R A} [na_semiring A] [na_algebra R A]

@[simp] lemma smul_mul_assoc (t : R) (a b : A) :
  (t • a) * b = t • (a * b) :=
na_algebra.smul_mul_assoc' t a b

@[simp] lemma mul_smul_comm (t : R) (a b : A) :
  a * (t • b) = t • (a * b) :=
na_algebra.mul_smul_comm' t a b

/-- The algebra multiplication as a bilinear map. -/
def mul_as_bilinear {R : Type u₁} {A : Type u₂} [comm_semiring R] [na_semiring A] [na_algebra R A] :
  A →ₗ[R] A →ₗ[R] A :=
linear_map.mk₂ R (*) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- If the underlying `na_semiring` is actually a `semiring` we have an `algebra`. -/
def to_algebra {R : Type u₁} {A : Type u₂} [comm_semiring R] [semiring A] [na_algebra R A] :
  algebra R A :=
algebra.of_semimodule smul_mul_assoc mul_smul_comm

end na_algebra

variables [na_semiring A] [na_algebra R A]
variables [na_semiring B] [na_algebra R B]
variables [na_semiring C] [na_algebra R C]

set_option old_structure_cmd true

/-- A morphism of non-associative algebras. -/
structure na_algebra_hom extends A →ₗ[R] B, mul_hom A B

attribute [nolint doc_blame] na_algebra_hom.to_linear_map
attribute [nolint doc_blame] na_algebra_hom.to_mul_hom

namespace na_algebra_hom

variables {R A B C}

instance : has_coe (na_algebra_hom R A B) (A →ₗ[R] B) := ⟨to_linear_map⟩

instance : has_coe (na_algebra_hom R A B) (mul_hom A B) := ⟨to_mul_hom⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (na_algebra_hom R A B) := ⟨_, to_fun⟩

initialize_simps_projections na_algebra_hom (to_fun → apply)

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : na_algebra_hom R A B) : A → B) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : na_algebra_hom R A B) :
  ((f : A →ₗ[R] B) : A → B) = f :=
rfl

@[simp, norm_cast] lemma coe_to_mul_hom (f : na_algebra_hom R A B) :
  ((f : mul_hom A B) : A → B) = f :=
rfl

@[simp] lemma map_smul (f : na_algebra_hom R A B) (c : R) (x : A) : f (c • x) = c • f x :=
linear_map.map_smul (f : A →ₗ[R] B) c x

@[simp] lemma map_add (f : na_algebra_hom R A B) (x y : A) : f (x + y) = (f x) + (f y) :=
linear_map.map_add (f : A →ₗ[R] B) x y

@[simp] lemma map_mul (f : na_algebra_hom R A B) (x y : A) : f (x * y) = (f x) * (f y) :=
mul_hom.map_mul (f : mul_hom A B) x y

@[simp] lemma map_zero (f : na_algebra_hom R A B) : f 0 = 0 := (f : A →ₗ[R] B).map_zero

instance : has_zero (na_algebra_hom R A B) := ⟨{ map_mul' := by simp, ..(0 : A →ₗ[R] B)}⟩

instance : inhabited (na_algebra_hom R A B) := ⟨0⟩

lemma coe_injective : function.injective (λ f : na_algebra_hom R A B, show A → B, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma ext {f g : na_algebra_hom R A B} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : na_algebra_hom R A B} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : na_algebra_hom R B C) (g : na_algebra_hom R A B) : na_algebra_hom R A C :=
{ ..mul_hom.comp (f : mul_hom B C) (g : mul_hom A B),
  ..linear_map.comp (f : B →ₗ[R] C) (g : A →ₗ[R] B) }

@[simp] lemma comp_apply (f : na_algebra_hom R B C) (g : na_algebra_hom R A B) (x : A) :
  f.comp g x = f (g x) := rfl

@[norm_cast]
lemma comp_coe (f : na_algebra_hom R B C) (g : na_algebra_hom R A B) :
  (f : B → C) ∘ (g : A → B) = f.comp g := rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : na_algebra_hom R A B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : na_algebra_hom R B A :=
{ map_mul' := λ x y,
  calc g (x * y) = g ((f (g x)) * (f (g y))) : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
             ... = g (f ((g x) * (g y))) : by rw map_mul
             ... = (g x) * (g y) : (h₁ _),
  ..linear_map.inverse (f : A →ₗ[R] B) g h₁ h₂ }

end na_algebra_hom

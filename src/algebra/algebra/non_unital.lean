/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.basic

/-!
# Non-unital, non-associative algebras

This files defines non-unital, non-associative algebras together with their morphisms and basic
lemmas to make them usable.

## Main definitions

  * `non_unital_non_assoc_algebra`
  * `non_unital_non_assoc_algebra_hom`

## Tags

non-unital, non-associative, algebra
-/

universes u₁ u₂ u₃ u₄

variables (R : Type u₁) (A : Type u₂) (B : Type u₃) (C : Type u₄) [semiring R]

/-- A not-necessarily-unital, not-necessarily-associative algebra. -/
@[protect_proj]
class non_unital_non_assoc_algebra [non_unital_non_assoc_semiring A] extends semimodule R A :=
(smul_mul_assoc' : ∀ (t : R) (a b : A), (t • a) * b = t • (a * b))
(mul_smul_comm' : ∀ (t : R) (a b : A), a * (t • b) = t • (a * b))

@[priority 200] -- see Note [lower instance priority]
instance semiring.to_non_unital_non_assoc_semiring [semiring A] : non_unital_non_assoc_semiring A :=
{ ..(infer_instance : semiring A) }

@[priority 200] -- see Note [lower instance priority]
instance algebra.to_non_unital_non_assoc_algebra (R : Type u₁)
  [comm_semiring R] [semiring A] [algebra R A] : non_unital_non_assoc_algebra R A :=
{ smul_mul_assoc' := algebra.smul_mul_assoc,
  mul_smul_comm'  := algebra.mul_smul_comm,
  ..algebra.to_semimodule }

namespace non_unital_non_assoc_algebra

variables {R A} [non_unital_non_assoc_semiring A] [non_unital_non_assoc_algebra R A]

lemma smul_mul_assoc (t : R) (a b : A) :
  (t • a) * b = t • (a * b) :=
non_unital_non_assoc_algebra.smul_mul_assoc' t a b

lemma mul_smul_comm (t : R) (a b : A) :
  a * (t • b) = t • (a * b) :=
non_unital_non_assoc_algebra.mul_smul_comm' t a b

/-- The algebra multiplication as a bilinear map. -/
def lmul {R : Type u₁} {A : Type u₂}
  [comm_semiring R] [non_unital_non_assoc_semiring A] [non_unital_non_assoc_algebra R A] :
  A →ₗ[R] module.End R A :=
linear_map.mk₂ R (*) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- If the underlying `non_unital_non_assoc_semiring` is actually a `semiring` we have an
`algebra`. -/
def to_algebra {R : Type u₁} {A : Type u₂}
  [comm_semiring R] [semiring A] [non_unital_non_assoc_algebra R A] : algebra R A :=
algebra.of_semimodule smul_mul_assoc mul_smul_comm

end non_unital_non_assoc_algebra

variables [non_unital_non_assoc_semiring A] [non_unital_non_assoc_algebra R A]
variables [non_unital_non_assoc_semiring B] [non_unital_non_assoc_algebra R B]
variables [non_unital_non_assoc_semiring C] [non_unital_non_assoc_algebra R C]

set_option old_structure_cmd true

/-- A morphism of non-associative algebras. -/
structure non_unital_non_assoc_algebra_hom extends A →ₗ[R] B, mul_hom A B

attribute [nolint doc_blame] non_unital_non_assoc_algebra_hom.to_linear_map
attribute [nolint doc_blame] non_unital_non_assoc_algebra_hom.to_mul_hom

namespace non_unital_non_assoc_algebra_hom

variables {R A B C}

instance {R : Type u₁} {A : Type u₂} {B : Type u₃}
  [comm_semiring R] [ring A] [ring B] [algebra R A] [algebra R B] :
  has_coe (A →ₐ[R] B) (non_unital_non_assoc_algebra_hom R A B) :=
⟨λ f, { to_fun    := f,
        map_smul' := f.map_smul,
        ..f, }⟩

instance : has_coe (non_unital_non_assoc_algebra_hom R A B) (A →ₗ[R] B) := ⟨to_linear_map⟩

instance : has_coe (non_unital_non_assoc_algebra_hom R A B) (mul_hom A B) := ⟨to_mul_hom⟩

lemma to_linear_map_eq_coe (f : non_unital_non_assoc_algebra_hom R A B) : f.to_linear_map = ↑f :=
rfl

lemma to_mul_hom_eq_coe (f : non_unital_non_assoc_algebra_hom R A B) : f.to_mul_hom = ↑f :=
rfl

/-- see Note [function coercion] -/
instance : has_coe_to_fun (non_unital_non_assoc_algebra_hom R A B) := ⟨_, to_fun⟩

initialize_simps_projections non_unital_non_assoc_algebra_hom (to_fun → apply)

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : non_unital_non_assoc_algebra_hom R A B) : A → B) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : non_unital_non_assoc_algebra_hom R A B) :
  ((f : A →ₗ[R] B) : A → B) = f :=
rfl

@[simp, norm_cast] lemma coe_to_mul_hom (f : non_unital_non_assoc_algebra_hom R A B) :
  ((f : mul_hom A B) : A → B) = f :=
rfl

@[simp] lemma map_smul (f : non_unital_non_assoc_algebra_hom R A B) (c : R) (x : A) :
  f (c • x) = c • f x :=
linear_map.map_smul (f : A →ₗ[R] B) c x

@[simp] lemma map_add (f : non_unital_non_assoc_algebra_hom R A B) (x y : A) :
  f (x + y) = (f x) + (f y) :=
linear_map.map_add (f : A →ₗ[R] B) x y

@[simp] lemma map_mul (f : non_unital_non_assoc_algebra_hom R A B) (x y : A) :
  f (x * y) = (f x) * (f y) :=
mul_hom.map_mul (f : mul_hom A B) x y

@[simp] lemma map_zero (f : non_unital_non_assoc_algebra_hom R A B) : f 0 = 0 :=
(f : A →ₗ[R] B).map_zero

instance : has_zero (non_unital_non_assoc_algebra_hom R A B) :=
⟨{ map_mul' := by simp,
   ..(0 : A →ₗ[R] B)}⟩

instance : inhabited (non_unital_non_assoc_algebra_hom R A B) := ⟨0⟩

lemma coe_injective :
  @function.injective (non_unital_non_assoc_algebra_hom R A B) (A → B) coe_fn :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma ext {f g : non_unital_non_assoc_algebra_hom R A B} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : non_unital_non_assoc_algebra_hom R A B} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : non_unital_non_assoc_algebra_hom R B C) (g : non_unital_non_assoc_algebra_hom R A B) :
  non_unital_non_assoc_algebra_hom R A C :=
{ ..mul_hom.comp (f : mul_hom B C) (g : mul_hom A B),
  ..linear_map.comp (f : B →ₗ[R] C) (g : A →ₗ[R] B) }

@[simp] lemma comp_apply
  (f : non_unital_non_assoc_algebra_hom R B C)
  (g : non_unital_non_assoc_algebra_hom R A B) (x : A) :
  f.comp g x = f (g x) :=
rfl

@[norm_cast]
lemma comp_coe
  (f : non_unital_non_assoc_algebra_hom R B C) (g : non_unital_non_assoc_algebra_hom R A B) :
  (f : B → C) ∘ (g : A → B) = f.comp g :=
rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : non_unital_non_assoc_algebra_hom R A B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  non_unital_non_assoc_algebra_hom R B A :=
{ ..mul_hom.inverse (f : mul_hom A B) g h₁ h₂,
  ..linear_map.inverse (f : A →ₗ[R] B) g h₁ h₂ }

end non_unital_non_assoc_algebra_hom

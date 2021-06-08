/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.basic

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two modules, each of which also carries a multiplication that is
compatible with the additive structure. The multiplications are not assumed to be associative or
unital, or even compatible with the scalar multiplication. In a typical application, the
multiplications and scalar multiplications will satisfy compatibility conditions making them into
algebras (albeit possibly non-associative and/or non-unital) but such conditions are not required to
make this definition.

## Main definitions

  * `non_unital_alg_hom`
  * `alg_hom.non_unital_alg_hom.has_coe`

## Tags

non-unital, algebra, morphism
-/

universes u v w w₁ w₂ w₃

variables (R : Type u) (A : Type v) (B : Type w) (C : Type w₁)

set_option old_structure_cmd true

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure non_unital_alg_hom [semiring R]
  [non_unital_non_assoc_semiring A] [module R A]
  [non_unital_non_assoc_semiring B] [module R B]
  extends A →ₗ[R] B, mul_hom A B

attribute [nolint doc_blame] non_unital_alg_hom.to_linear_map
attribute [nolint doc_blame] non_unital_alg_hom.to_mul_hom

initialize_simps_projections non_unital_alg_hom (to_fun → apply)

namespace non_unital_alg_hom

variables {R A B C} [semiring R]
variables [non_unital_non_assoc_semiring A] [module R A]
variables [non_unital_non_assoc_semiring B] [module R B]
variables [non_unital_non_assoc_semiring C] [module R C]

/-- see Note [function coercion] -/
instance : has_coe_to_fun (non_unital_alg_hom R A B) := ⟨_, to_fun⟩

lemma coe_injective :
  @function.injective (non_unital_alg_hom R A B) (A → B) coe_fn :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma ext {f g : non_unital_alg_hom R A B} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : non_unital_alg_hom R A B} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : non_unital_alg_hom R A B) : A → B) = f :=
rfl

@[simp] lemma mk_coe (f : non_unital_alg_hom R A B) (h₁ h₂ h₃) :
  (⟨f, h₁, h₂, h₃⟩ : non_unital_alg_hom R A B) = f :=
by { ext, refl, }

instance : has_coe (non_unital_alg_hom R A B) (A →ₗ[R] B) := ⟨to_linear_map⟩

instance : has_coe (non_unital_alg_hom R A B) (mul_hom A B) := ⟨to_mul_hom⟩

@[simp] lemma to_linear_map_eq_coe (f : non_unital_alg_hom R A B) : f.to_linear_map = ↑f :=
rfl

@[simp] lemma to_mul_hom_eq_coe (f : non_unital_alg_hom R A B) : f.to_mul_hom = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : non_unital_alg_hom R A B) :
  ((f : A →ₗ[R] B) : A → B) = f :=
rfl

@[simp, norm_cast] lemma coe_to_mul_hom (f : non_unital_alg_hom R A B) :
  ((f : mul_hom A B) : A → B) = f :=
rfl

@[norm_cast] lemma coe_linear_map_mk (f : non_unital_alg_hom R A B) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : non_unital_alg_hom R A B) : A →ₗ[R] B) = ⟨f, h₁, h₂⟩ :=
by { ext, refl, }

@[norm_cast] lemma coe_mul_hom_mk (f : non_unital_alg_hom R A B) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : non_unital_alg_hom R A B) : mul_hom A B) = ⟨f, h₃⟩ :=
by { ext, refl, }

@[simp] lemma map_smul (f : non_unital_alg_hom R A B) (c : R) (x : A) :
  f (c • x) = c • f x :=
f.to_linear_map.map_smul c x

@[simp] lemma map_add (f : non_unital_alg_hom R A B) (x y : A) :
  f (x + y) = (f x) + (f y) :=
f.to_linear_map.map_add x y

@[simp] lemma map_mul (f : non_unital_alg_hom R A B) (x y : A) :
  f (x * y) = (f x) * (f y) :=
f.to_mul_hom.map_mul x y

@[simp] lemma map_zero (f : non_unital_alg_hom R A B) : f 0 = 0 :=
f.to_linear_map.map_zero

instance : has_zero (non_unital_alg_hom R A B) :=
⟨{ map_mul' := by simp,
   .. (0 : A →ₗ[R] B)}⟩

instance : has_one (non_unital_alg_hom R A A) :=
⟨{ map_mul' := by simp,
   .. (1 : A →ₗ[R] A) }⟩

@[simp] lemma coe_zero : ((0 : non_unital_alg_hom R A B) : A → B) = 0 := rfl

@[simp] lemma coe_one : ((1 : non_unital_alg_hom R A A) : A → A) = id := rfl

lemma zero_apply (a : A) : (0 : non_unital_alg_hom R A B) a = 0 := rfl

lemma one_apply (a : A) : (1 : non_unital_alg_hom R A A) a = a := rfl

instance : inhabited (non_unital_alg_hom R A B) := ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : non_unital_alg_hom R B C) (g : non_unital_alg_hom R A B) : non_unital_alg_hom R A C :=
{ .. mul_hom.comp (f : mul_hom B C) (g : mul_hom A B),
  .. linear_map.comp (f : B →ₗ[R] C) (g : A →ₗ[R] B) }

@[simp, norm_cast] lemma coe_comp (f : non_unital_alg_hom R B C) (g : non_unital_alg_hom R A B) :
  (f.comp g : A → C) = (f : B → C) ∘ (g : A → B) :=
rfl

lemma comp_apply (f : non_unital_alg_hom R B C) (g : non_unital_alg_hom R A B) (x : A) :
  f.comp g x = f (g x) :=
rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : non_unital_alg_hom R A B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  non_unital_alg_hom R B A :=
{ .. mul_hom.inverse (f : mul_hom A B) g h₁ h₂,
  .. linear_map.inverse (f : A →ₗ[R] B) g h₁ h₂ }

@[simp] lemma coe_inverse (f : non_unital_alg_hom R A B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  (inverse f g h₁ h₂ : B → A) = g :=
rfl

end non_unital_alg_hom

namespace alg_hom

variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

instance non_unital_alg_hom.has_coe : has_coe (A →ₐ[R] B) (non_unital_alg_hom R A B) :=
⟨λ f, { map_smul' := f.map_smul, .. f, }⟩

@[simp, norm_cast] lemma coe_to_non_unital_alg_hom (f : A →ₐ[R] B) :
  ((f : non_unital_alg_hom R A B) : A → B) = f :=
rfl

end alg_hom

/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.hom

/-!
# Morphisms of non-unital algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines morphisms between two types, each of which carries:
 * an addition,
 * an additive zero,
 * a multiplication,
 * a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `has_mul` instead of `group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `non_unital_alg_hom`.

TODO: add `non_unital_alg_equiv` when needed.

## Main definitions

  * `non_unital_alg_hom`
  * `alg_hom.to_non_unital_alg_hom`

## Tags

non-unital, algebra, morphism
-/

universes u v w w₁ w₂ w₃

variables (R : Type u) (A : Type v) (B : Type w) (C : Type w₁)

set_option old_structure_cmd true

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure non_unital_alg_hom [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B]
  extends A →+[R] B, A →ₙ* B

infixr ` →ₙₐ `:25 := non_unital_alg_hom _
notation A ` →ₙₐ[`:25 R `] ` B := non_unital_alg_hom R A B

attribute [nolint doc_blame] non_unital_alg_hom.to_distrib_mul_action_hom
attribute [nolint doc_blame] non_unital_alg_hom.to_mul_hom

/-- `non_unital_alg_hom_class F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class non_unital_alg_hom_class (F : Type*) (R : out_param Type*) (A : out_param Type*)
  (B : out_param Type*) [monoid R]
  [non_unital_non_assoc_semiring A] [non_unital_non_assoc_semiring B]
  [distrib_mul_action R A] [distrib_mul_action R B]
  extends distrib_mul_action_hom_class F R A B, mul_hom_class F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] non_unital_alg_hom_class.to_mul_hom_class

namespace non_unital_alg_hom_class

-- `R` becomes a metavariable but that's fine because it's an `out_param`
@[priority 100, nolint dangerous_instance] -- See note [lower instance priority]
instance non_unital_alg_hom_class.to_non_unital_ring_hom_class {F R A B : Type*} [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B]
  [non_unital_alg_hom_class F R A B] : non_unital_ring_hom_class F A B :=
{ coe := coe_fn, ..‹non_unital_alg_hom_class F R A B› }

variables [semiring R]
  [non_unital_non_assoc_semiring A] [module R A]
  [non_unital_non_assoc_semiring B] [module R B]

@[priority 100] -- see Note [lower instance priority]
instance {F : Type*} [non_unital_alg_hom_class F R A B] : linear_map_class F R A B :=
{ map_smulₛₗ := distrib_mul_action_hom_class.map_smul,
  ..‹non_unital_alg_hom_class F R A B› }

instance {F R A B : Type*} [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B]
  [non_unital_alg_hom_class F R A B] : has_coe_t F (A →ₙₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_smul' := map_smul f,
    .. (f : A →ₙ+* B) } }

end non_unital_alg_hom_class

namespace non_unital_alg_hom

variables {R A B C} [monoid R]
variables [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R B]
variables [non_unital_non_assoc_semiring C] [distrib_mul_action R C]

/-- see Note [function coercion] -/
instance : has_coe_to_fun (A →ₙₐ[R] B) (λ _, A → B) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe (f : A →ₙₐ[R] B) : f.to_fun = ⇑f := rfl

initialize_simps_projections non_unital_alg_hom (to_fun → apply)

@[simp, protected] lemma coe_coe {F : Type*} [non_unital_alg_hom_class F R A B] (f : F) :
  ⇑(f : A →ₙₐ[R] B) = f := rfl

lemma coe_injective :
  @function.injective (A →ₙₐ[R] B) (A → B) coe_fn :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

instance : non_unital_alg_hom_class (A →ₙₐ[R] B) R A B :=
{ coe := to_fun,
  coe_injective' := coe_injective,
  map_smul := λ f, f.map_smul',
  map_add := λ f, f.map_add',
  map_zero := λ f, f.map_zero',
  map_mul := λ f, f.map_mul' }

@[ext] lemma ext {f g : A →ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : A →ₙₐ[R] B} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

lemma congr_fun {f g : A →ₙₐ[R] B} (h : f = g) (x : A) : f x = g x := h ▸ rfl

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) : A → B) = f :=
rfl

@[simp] lemma mk_coe (f : A →ₙₐ[R] B) (h₁ h₂ h₃ h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) = f :=
by { ext, refl, }

instance : has_coe (A →ₙₐ[R] B) (A →+[R] B) :=
⟨to_distrib_mul_action_hom⟩

instance : has_coe (A →ₙₐ[R] B) (A →ₙ* B) := ⟨to_mul_hom⟩

@[simp] lemma to_distrib_mul_action_hom_eq_coe (f : A →ₙₐ[R] B) :
  f.to_distrib_mul_action_hom = ↑f :=
rfl

@[simp] lemma to_mul_hom_eq_coe (f : A →ₙₐ[R] B) : f.to_mul_hom = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_distrib_mul_action_hom (f : A →ₙₐ[R] B) :
  ((f : A →+[R] B) : A → B) = f :=
rfl

@[simp, norm_cast] lemma coe_to_mul_hom (f : A →ₙₐ[R] B) :
  ((f : A →ₙ* B) : A → B) = f :=
rfl

lemma to_distrib_mul_action_hom_injective {f g : A →ₙₐ[R] B}
  (h : (f : A →+[R] B) = (g : A →+[R] B)) : f = g :=
by { ext a, exact distrib_mul_action_hom.congr_fun h a, }

lemma to_mul_hom_injective {f g : A →ₙₐ[R] B}
  (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g :=
by { ext a, exact mul_hom.congr_fun h a, }

@[norm_cast] lemma coe_distrib_mul_action_hom_mk (f : A →ₙₐ[R] B) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) : A →+[R] B) =
  ⟨f, h₁, h₂, h₃⟩ :=
by { ext, refl, }

@[norm_cast] lemma coe_mul_hom_mk (f : A →ₙₐ[R] B) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) : A →ₙ* B) = ⟨f, h₄⟩ :=
by { ext, refl, }

@[simp] protected lemma map_smul (f : A →ₙₐ[R] B) (c : R) (x : A) :
  f (c • x) = c • f x := map_smul _ _ _

@[simp] protected lemma map_add (f : A →ₙₐ[R] B) (x y : A) :
  f (x + y) = (f x) + (f y) := map_add _ _ _

@[simp] protected lemma map_mul (f : A →ₙₐ[R] B) (x y : A) :
  f (x * y) = (f x) * (f y) := map_mul _ _ _

@[simp] protected lemma map_zero (f : A →ₙₐ[R] B) : f 0 = 0 := map_zero _

instance : has_zero (A →ₙₐ[R] B) :=
⟨{ map_mul' := by simp,
   .. (0 : A →+[R] B) }⟩

instance : has_one (A →ₙₐ[R] A) :=
⟨{ map_mul' := by simp,
   .. (1 : A →+[R] A) }⟩

@[simp] lemma coe_zero : ((0 : A →ₙₐ[R] B) : A → B) = 0 := rfl

@[simp] lemma coe_one : ((1 : A →ₙₐ[R] A) : A → A) = id := rfl

lemma zero_apply (a : A) : (0 : A →ₙₐ[R] B) a = 0 := rfl

lemma one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a := rfl

instance : inhabited (A →ₙₐ[R] B) := ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) : A →ₙₐ[R] C :=
{ .. (f : B →ₙ* C).comp (g : A →ₙ* B),
  .. (f : B →+[R] C).comp (g : A →+[R] B) }

@[simp, norm_cast] lemma coe_comp (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) :
  (f.comp g : A → C) = (f : B → C) ∘ (g : A → B) :=
rfl

lemma comp_apply (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) (x : A) :
  f.comp g x = f (g x) :=
rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : A →ₙₐ[R] B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  B →ₙₐ[R] A :=
{ .. (f : A →ₙ* B).inverse g h₁ h₂,
  .. (f : A →+[R] B).inverse g h₁ h₂ }

@[simp] lemma coe_inverse (f : A →ₙₐ[R] B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  (inverse f g h₁ h₂ : B → A) = g :=
rfl

/-! ### Operations on the product type

Note that much of this is copied from [`linear_algebra/prod`](../../linear_algebra/prod). -/

section prod

variables (R A B)
/-- The first projection of a product is a non-unital alg_hom. -/
@[simps]
def fst : A × B →ₙₐ[R] A :=
{ to_fun := prod.fst,
  map_zero' := rfl, map_add' := λ x y, rfl, map_smul' := λ x y, rfl, map_mul' := λ x y, rfl }

/-- The second projection of a product is a non-unital alg_hom. -/
@[simps]
def snd : A × B →ₙₐ[R] B :=
{ to_fun := prod.snd,
  map_zero' := rfl, map_add' := λ x y, rfl, map_smul' := λ x y, rfl, map_mul' := λ x y, rfl }

variables {R A B}

/-- The prod of two morphisms is a morphism. -/
@[simps] def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (A →ₙₐ[R] B × C) :=
{ to_fun    := pi.prod f g,
  map_zero' := by simp only [pi.prod, prod.zero_eq_mk, map_zero],
  map_add'  := λ x y, by simp only [pi.prod, prod.mk_add_mk, map_add],
  map_mul'  := λ x y, by simp only [pi.prod, prod.mk_mul_mk, map_mul],
  map_smul' := λ c x, by simp only [pi.prod, prod.smul_mk, map_smul, ring_hom.id_apply] }

lemma coe_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp] theorem fst_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) :
  (fst R B C).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) :
  (snd R B C).comp (prod f g) = g := by ext; refl

@[simp] theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
coe_injective pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps] def prod_equiv : ((A →ₙₐ[R] B) × (A →ₙₐ[R] C)) ≃ (A →ₙₐ[R] B × C) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((fst _ _ _).comp f, (snd _ _ _).comp f),
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

variables (R A B)

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →ₙₐ[R] A × B := prod 1 0

/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →ₙₐ[R] A × B := prod 0 1

variables {R A B}

@[simp] theorem coe_inl : (inl R A B : A → A × B) = λ x, (x, 0) := rfl
theorem inl_apply (x : A) : inl R A B x = (x, 0) := rfl

@[simp] theorem coe_inr : (inr R A B : B → A × B) = prod.mk 0 := rfl
theorem inr_apply (x : B) : inr R A B x = (0, x) := rfl

end prod

end non_unital_alg_hom

/-! ### Interaction with `alg_hom` -/

namespace alg_hom

variables {R A B} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

@[priority 100] -- see Note [lower instance priority]
instance {F : Type*} [alg_hom_class F R A B] : non_unital_alg_hom_class F R A B :=
{ map_smul := map_smul,
  ..‹alg_hom_class F R A B› }

/-- A unital morphism of algebras is a `non_unital_alg_hom`. -/
def to_non_unital_alg_hom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
{ map_smul' := map_smul f, .. f, }

instance non_unital_alg_hom.has_coe : has_coe (A →ₐ[R] B) (A →ₙₐ[R] B) :=
⟨to_non_unital_alg_hom⟩

@[simp] lemma to_non_unital_alg_hom_eq_coe (f : A →ₐ[R] B) : f.to_non_unital_alg_hom = f :=
rfl

@[simp, norm_cast] lemma coe_to_non_unital_alg_hom (f : A →ₐ[R] B) :
  ((f : A →ₙₐ[R] B) : A → B) = f :=
rfl

end alg_hom

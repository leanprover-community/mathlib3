/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.hom.non_unital_alg
import algebra.star.prod
import algebra.algebra.prod

/-!
# Morphisms of star algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines morphisms between `R`-algebras (unital or non-unital) `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms, namely `star_alg_hom` and
`non_unital_star_alg_hom` are direct extensions of their non-`star`red counterparts with a field
`map_star` which guarantees they preserve the star operation. We keep the type classes as generic
as possible, in keeping with the definition of `non_unital_alg_hom` in the non-unital case. In this
file, we only assume `has_star` unless we want to talk about the zero map as a
`non_unital_star_alg_hom`, in which case we need `star_add_monoid`. Note that the scalar ring `R`
is not required to have a star operation, nor do we need `star_ring` or `star_module` structures on
`A` and `B`.

As with `non_unital_alg_hom`, in the non-unital case the multiplications are not assumed to be
associative or unital, or even to be compatible with the scalar actions. In a typical application,
the operations will satisfy compatibility conditions making them into algebras (albeit possibly
non-associative and/or non-unital) but such conditions are not required here for the definitions.

The primary impetus for defining these types is that they constitute the morphisms in the categories
of unital C⋆-algebras (with `star_alg_hom`s) and of C⋆-algebras (with `non_unital_star_alg_hom`s).

TODO: add `star_alg_equiv`.

## Main definitions

  * `non_unital_alg_hom`
  * `star_alg_hom`

## Tags

non-unital, algebra, morphism, star
-/

set_option old_structure_cmd true

/-! ### Non-unital star algebra homomorphisms -/

/-- A *non-unital ⋆-algebra homomorphism* is a non-unital algebra homomorphism between
non-unital `R`-algebras `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
structure non_unital_star_alg_hom (R A B : Type*) [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [has_star A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [has_star B]
  extends A →ₙₐ[R] B :=
(map_star' : ∀ a : A, to_fun (star a) = star (to_fun a))

infixr ` →⋆ₙₐ `:25 := non_unital_star_alg_hom _
notation A ` →⋆ₙₐ[`:25 R `] ` B := non_unital_star_alg_hom R A B

/-- Reinterpret a non-unital star algebra homomorphism as a non-unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc non_unital_star_alg_hom.to_non_unital_alg_hom

/-- `non_unital_star_alg_hom_class F R A B` asserts `F` is a type of bundled non-unital ⋆-algebra
homomorphisms from `A` to `B`. -/
class non_unital_star_alg_hom_class (F : Type*) (R : out_param Type*) (A : out_param Type*)
  (B : out_param Type*) [monoid R] [has_star A] [has_star B]
  [non_unital_non_assoc_semiring A] [non_unital_non_assoc_semiring B]
  [distrib_mul_action R A] [distrib_mul_action R B]
  extends non_unital_alg_hom_class F R A B, star_hom_class F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] non_unital_star_alg_hom_class.to_star_hom_class

namespace non_unital_star_alg_hom_class

variables {F R A B : Type*} [monoid R]
variables [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [has_star A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [has_star B]

instance [non_unital_star_alg_hom_class F R A B] : has_coe_t F (A →⋆ₙₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_star' := map_star f,
    .. (f : A →ₙₐ[R] B) }}

end non_unital_star_alg_hom_class

namespace non_unital_star_alg_hom

section basic

variables {R A B C D : Type*} [monoid R]
variables [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [has_star A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [has_star B]
variables [non_unital_non_assoc_semiring C] [distrib_mul_action R C] [has_star C]
variables [non_unital_non_assoc_semiring D] [distrib_mul_action R D] [has_star D]

instance : non_unital_star_alg_hom_class (A →⋆ₙₐ[R] B) R A B :=
{ coe := to_fun,
  coe_injective' := by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr,
  map_smul := λ f, f.map_smul',
  map_add := λ f, f.map_add',
  map_zero := λ f, f.map_zero',
  map_mul := λ f, f.map_mul',
  map_star := λ f, f.map_star' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (A →⋆ₙₐ[R] B) (λ _, A → B) := fun_like.has_coe_to_fun

initialize_simps_projections non_unital_star_alg_hom (to_fun → apply)

@[simp, protected] lemma coe_coe {F : Type*} [non_unital_star_alg_hom_class F R A B] (f : F) :
  ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

@[simp] lemma coe_to_non_unital_alg_hom {f : A →⋆ₙₐ[R] B} :
  (f.to_non_unital_alg_hom : A → B) = f := rfl

@[ext] lemma ext {f g : A →⋆ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- Copy of a `non_unital_star_alg_hom` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₙₐ[R] B :=
{ to_fun := f',
  map_smul' := h.symm ▸ map_smul f,
  map_zero' := h.symm ▸ map_zero f,
  map_add' := h.symm ▸ map_add f,
  map_mul' := h.symm ▸ map_mul f,
  map_star' := h.symm ▸ map_star f }

@[simp] lemma coe_copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅) :
  ((⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
rfl

@[simp] lemma mk_coe (f : A →⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →⋆ₙₐ[R] B) = f :=
by { ext, refl, }

section
variables (R A)
/-- The identity as a non-unital ⋆-algebra homomorphism. -/
protected def id : A →⋆ₙₐ[R] A :=
{ map_star' := λ x, rfl, .. (1 : A →ₙₐ[R] A) }

@[simp] lemma coe_id : ⇑(non_unital_star_alg_hom.id R A) = id := rfl
end

/-- The composition of non-unital ⋆-algebra homomorphisms, as a non-unital ⋆-algebra
homomorphism. -/
def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
{ map_star' := by simp only [map_star, non_unital_alg_hom.to_fun_eq_coe, eq_self_iff_true,
    non_unital_alg_hom.coe_comp, coe_to_non_unital_alg_hom, function.comp_app, forall_const],
  .. f.to_non_unital_alg_hom.comp g.to_non_unital_alg_hom }

@[simp] lemma coe_comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g := rfl

@[simp] lemma comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) := rfl

@[simp] lemma comp_assoc (f : C →⋆ₙₐ[R] D) (g : B →⋆ₙₐ[R] C) (h : A →⋆ₙₐ[R] B) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp] lemma id_comp (f : A →⋆ₙₐ[R] B) : (non_unital_star_alg_hom.id _ _).comp f = f :=
ext $ λ _, rfl

@[simp] lemma comp_id (f : A →⋆ₙₐ[R] B) : f.comp (non_unital_star_alg_hom.id _ _) = f :=
ext $ λ _, rfl

instance : monoid (A →⋆ₙₐ[R] A) :=
{ mul := comp,
  mul_assoc := comp_assoc,
  one := non_unital_star_alg_hom.id R A,
  one_mul := id_comp,
  mul_one := comp_id, }

@[simp] lemma coe_one : ((1 : A →⋆ₙₐ[R] A) : A → A) = id := rfl
lemma one_apply (a : A) : (1 : A →⋆ₙₐ[R] A) a = a := rfl

end basic

section zero
-- the `zero` requires extra type class assumptions because we need `star_zero`
variables {R A B C D : Type*} [monoid R]
variables [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [star_add_monoid A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [star_add_monoid B]

instance : has_zero (A →⋆ₙₐ[R] B) :=
⟨{ map_star' := by simp, .. (0 : non_unital_alg_hom R A B) }⟩

instance : inhabited (A →⋆ₙₐ[R] B) := ⟨0⟩

instance : monoid_with_zero (A →⋆ₙₐ[R] A) :=
{ zero_mul := λ f, ext $ λ x, rfl,
  mul_zero := λ f, ext $ λ x, map_zero f,
  .. non_unital_star_alg_hom.monoid,
  .. non_unital_star_alg_hom.has_zero }

@[simp] lemma coe_zero : ((0 : A →⋆ₙₐ[R] B) : A → B) = 0 := rfl
lemma zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 := rfl

end zero

end non_unital_star_alg_hom

/-! ### Unital star algebra homomorphisms -/

section unital

/-- A *⋆-algebra homomorphism* is an algebra homomorphism between `R`-algebras `A` and `B`
equipped with a `star` operation, and this homomorphism is also `star`-preserving. -/
structure star_alg_hom (R A B: Type*) [comm_semiring R] [semiring A] [algebra R A] [has_star A]
  [semiring B] [algebra R B] [has_star B] extends alg_hom R A B :=
(map_star' : ∀ x : A, to_fun (star x) = star (to_fun x))

infixr ` →⋆ₐ `:25 := star_alg_hom _
notation A ` →⋆ₐ[`:25 R `] ` B := star_alg_hom R A B

/-- Reinterpret a unital star algebra homomorphism as a unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc star_alg_hom.to_alg_hom

/-- `star_alg_hom_class F R A B` states that `F` is a type of ⋆-algebra homomorphisms.

You should also extend this typeclass when you extend `star_alg_hom`. -/
class star_alg_hom_class (F : Type*) (R : out_param Type*) (A : out_param Type*)
  (B : out_param Type*) [comm_semiring R] [semiring A] [algebra R A] [has_star A]
  [semiring B] [algebra R B] [has_star B] extends alg_hom_class F R A B, star_hom_class F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] star_alg_hom_class.to_star_hom_class

namespace star_alg_hom_class

variables (F R A B : Type*) [comm_semiring R] [semiring A] [algebra R A] [has_star A]
variables [semiring B] [algebra R B] [has_star B] [hF : star_alg_hom_class F R A B]
include hF

@[priority 100] /- See note [lower instance priority] -/
instance to_non_unital_star_alg_hom_class : non_unital_star_alg_hom_class F R A B :=
{ map_smul := map_smul,
  .. star_alg_hom_class.to_alg_hom_class F R A B,
  .. star_alg_hom_class.to_star_hom_class F R A B, }

instance : has_coe_t F (A →⋆ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_star' := map_star f,
    ..(f : A →ₐ[R] B) } }

end star_alg_hom_class

namespace star_alg_hom

variables {F R A B C D : Type*} [comm_semiring R]
  [semiring A] [algebra R A] [has_star A]
  [semiring B] [algebra R B] [has_star B]
  [semiring C] [algebra R C] [has_star C]
  [semiring D] [algebra R D] [has_star D]

instance : star_alg_hom_class (A →⋆ₐ[R] B) R A B :=
{ coe :=  λ f, f.to_fun,
  coe_injective' := λ f g h,
  begin
    obtain ⟨_, _, _, _, _, _, _⟩ := f;
    obtain ⟨_, _, _, _, _, _, _⟩ := g;
    congr'
  end,
  map_mul := map_mul',
  map_one := map_one',
  map_add := map_add',
  map_zero := map_zero',
  commutes := commutes',
  map_star := map_star' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (A →⋆ₐ[R] B) (λ _, A → B) := fun_like.has_coe_to_fun

@[simp, protected] lemma coe_coe {F : Type*} [star_alg_hom_class F R A B] (f : F) :
  ⇑(f : A →⋆ₐ[R] B) = f := rfl

initialize_simps_projections star_alg_hom (to_fun → apply)

@[simp] lemma coe_to_alg_hom {f : A →⋆ₐ[R] B} :
  (f.to_alg_hom : A → B) = f := rfl

@[ext] lemma ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- Copy of a `star_alg_hom` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₐ[R] B :=
{ to_fun := f',
  map_one' := h.symm ▸ map_one f ,
  map_mul' := h.symm ▸ map_mul f,
  map_zero' := h.symm ▸ map_zero f,
  map_add' := h.symm ▸ map_add f,
  commutes' := h.symm ▸ alg_hom_class.commutes f,
  map_star' := h.symm ▸ map_star f }

@[simp] lemma coe_copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅ h₆) :
  ((⟨f, h₁, h₂, h₃, h₄, h₅, h₆⟩ : A →⋆ₐ[R] B) : A → B) = f :=
rfl

@[simp] lemma mk_coe (f : A →⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) :
  (⟨f, h₁, h₂, h₃, h₄, h₅, h₆⟩ : A →⋆ₐ[R] B) = f :=
by { ext, refl, }

section
variables (R A)
/-- The identity as a `star_alg_hom`. -/
protected def id : A →⋆ₐ[R] A := { map_star' := λ x, rfl, .. alg_hom.id _ _ }
@[simp] lemma coe_id : ⇑(star_alg_hom.id R A) = id := rfl
end

instance : inhabited (A →⋆ₐ[R] A) := ⟨star_alg_hom.id R A⟩

/-- The composition of ⋆-algebra homomorphisms, as a ⋆-algebra homomorphism. -/
def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
{ map_star' := by simp only [map_star, alg_hom.to_fun_eq_coe, alg_hom.coe_comp, coe_to_alg_hom,
    function.comp_app, eq_self_iff_true, forall_const],
  .. f.to_alg_hom.comp g.to_alg_hom }

@[simp] lemma coe_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g := rfl

@[simp] lemma comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : comp f g a = f (g a) := rfl

@[simp] lemma comp_assoc (f : C →⋆ₐ[R] D) (g : B →⋆ₐ[R] C) (h : A →⋆ₐ[R] B) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp] lemma id_comp (f : A →⋆ₐ[R] B) : (star_alg_hom.id _ _).comp f = f := ext $ λ _, rfl

@[simp] lemma comp_id (f : A →⋆ₐ[R] B) : f.comp (star_alg_hom.id _ _) = f := ext $ λ _, rfl

instance : monoid (A →⋆ₐ[R] A) :=
{ mul := comp,
  mul_assoc := comp_assoc,
  one := star_alg_hom.id R A,
  one_mul := id_comp,
  mul_one := comp_id }

/-- A unital morphism of ⋆-algebras is a `non_unital_star_alg_hom`. -/
def to_non_unital_star_alg_hom (f : A →⋆ₐ[R] B) : A →⋆ₙₐ[R] B :=
{ map_smul' := map_smul f, .. f, }

@[simp] lemma coe_to_non_unital_star_alg_hom (f : A →⋆ₐ[R] B) :
  (f.to_non_unital_star_alg_hom : A → B) = f :=
rfl

end star_alg_hom

end unital

/-! ### Operations on the product type

Note that this is copied from [`algebra/hom/non_unital_alg`](non_unital_alg). -/

namespace non_unital_star_alg_hom

section prod

variables (R A B C : Type*) [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [has_star A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [has_star B]
  [non_unital_non_assoc_semiring C] [distrib_mul_action R C] [has_star C]

/-- The first projection of a product is a non-unital ⋆-algebra homomoprhism. -/
@[simps]
def fst : A × B →⋆ₙₐ[R] A :=
{ map_star' := λ x, rfl, .. non_unital_alg_hom.fst R A B }

/-- The second projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps]
def snd : A × B →⋆ₙₐ[R] B :=
{ map_star' := λ x, rfl, .. non_unital_alg_hom.snd R A B }

variables {R A B C}

/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps] def prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (A →⋆ₙₐ[R] B × C) :=
{ map_star' := λ x, by simp [map_star, prod.star_def],
  .. f.to_non_unital_alg_hom.prod g.to_non_unital_alg_hom }

lemma coe_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp] theorem fst_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) :
  (fst R B C).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) :
  (snd R B C).comp (prod f g) = g := by ext; refl

@[simp] theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
fun_like.coe_injective pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps] def prod_equiv : ((A →⋆ₙₐ[R] B) × (A →⋆ₙₐ[R] C)) ≃ (A →⋆ₙₐ[R] B × C) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((fst _ _ _).comp f, (snd _ _ _).comp f),
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

end prod

section inl_inr

variables (R A B C : Type*) [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [star_add_monoid A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [star_add_monoid B]
  [non_unital_non_assoc_semiring C] [distrib_mul_action R C] [star_add_monoid C]

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →⋆ₙₐ[R] A × B := prod 1 0

/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →⋆ₙₐ[R] A × B := prod 0 1

variables {R A B}

@[simp] theorem coe_inl : (inl R A B : A → A × B) = λ x, (x, 0) := rfl
theorem inl_apply (x : A) : inl R A B x = (x, 0) := rfl

@[simp] theorem coe_inr : (inr R A B : B → A × B) = prod.mk 0 := rfl
theorem inr_apply (x : B) : inr R A B x = (0, x) := rfl

end inl_inr

end non_unital_star_alg_hom

namespace star_alg_hom

variables (R A B C : Type*) [comm_semiring R]
  [semiring A] [algebra R A] [has_star A]
  [semiring B] [algebra R B] [has_star B]
  [semiring C] [algebra R C] [has_star C]

/-- The first projection of a product is a ⋆-algebra homomoprhism. -/
@[simps]
def fst : A × B →⋆ₐ[R] A :=
{ map_star' := λ x, rfl, .. alg_hom.fst R A B }

/-- The second projection of a product is a ⋆-algebra homomorphism. -/
@[simps]
def snd : A × B →⋆ₐ[R] B :=
{ map_star' := λ x, rfl, .. alg_hom.snd R A B }

variables {R A B C}

/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps] def prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (A →⋆ₐ[R] B × C) :=
{ map_star' := λ x, by simp [prod.star_def, map_star],
 .. f.to_alg_hom.prod g.to_alg_hom }

lemma coe_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp] theorem fst_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) :
  (fst R B C).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) :
  (snd R B C).comp (prod f g) = g := by ext; refl

@[simp] theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
fun_like.coe_injective pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps] def prod_equiv : ((A →⋆ₐ[R] B) × (A →⋆ₐ[R] C)) ≃ (A →⋆ₐ[R] B × C) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((fst _ _ _).comp f, (snd _ _ _).comp f),
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

end star_alg_hom

/-! ### Star algebra equivalences -/

/-- A *⋆-algebra* equivalence is an equivalence preserving addition, multiplication, scalar
multiplication and the star operation, which allows for considering both unital and non-unital
equivalences with a single structure. Currently, `alg_equiv` requires unital algebras, which is
why this structure does not extend it. -/
structure star_alg_equiv (R A B : Type*) [has_add A] [has_mul A] [has_smul R A] [has_star A]
  [has_add B] [has_mul B] [has_smul R B] [has_star B] extends A ≃+* B :=
(map_star' : ∀ a : A, to_fun (star a) = star (to_fun a))
(map_smul' : ∀ (r : R) (a : A), to_fun (r • a) = r • to_fun a)

infixr ` ≃⋆ₐ `:25 := star_alg_equiv _
notation A ` ≃⋆ₐ[`:25 R `] ` B := star_alg_equiv R A B

/-- Reinterpret a star algebra equivalence as a `ring_equiv` by forgetting the interaction with
the star operation and scalar multiplication. -/
add_decl_doc star_alg_equiv.to_ring_equiv

/-- `star_alg_equiv_class F R A B` asserts `F` is a type of bundled ⋆-algebra equivalences between
`A` and `B`.

You should also extend this typeclass when you extend `star_alg_equiv`. -/
class star_alg_equiv_class (F : Type*) (R : out_param Type*) (A : out_param Type*)
  (B : out_param Type*) [has_add A] [has_mul A] [has_smul R A] [has_star A] [has_add B] [has_mul B]
  [has_smul R B] [has_star B] extends ring_equiv_class F A B :=
(map_star : ∀ (f : F) (a : A), f (star a) = star (f a))
(map_smul : ∀ (f : F) (r : R) (a : A), f (r • a) = r • f a)

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] star_alg_equiv_class.to_ring_equiv_class

namespace star_alg_equiv_class

@[priority 50] -- See note [lower instance priority]
instance {F R A B : Type*} [has_add A] [has_mul A] [has_smul R A] [has_star A] [has_add B]
  [has_mul B] [has_smul R B] [has_star B] [hF : star_alg_equiv_class F R A B] :
  star_hom_class F A B :=
{ coe := λ f, f,
  coe_injective' := fun_like.coe_injective,
  .. hF }

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] star_alg_equiv_class.star_hom_class

@[priority 50] -- See note [lower instance priority]
instance {F R A B : Type*} [has_add A] [has_mul A] [has_star A] [has_smul R A] [has_add B]
  [has_mul B] [has_smul R B] [has_star B] [hF : star_alg_equiv_class F R A B] :
  smul_hom_class F R A B :=
{ coe := λ f, f,
  coe_injective' := fun_like.coe_injective,
  .. hF }

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] star_alg_equiv_class.smul_hom_class

@[priority 100] -- See note [lower instance priority]
instance {F R A B : Type*} [monoid R] [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  [has_star A] [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [has_star B]
  [hF : star_alg_equiv_class F R A B] : non_unital_star_alg_hom_class F R A B :=
{ coe := λ f, f,
  coe_injective' := fun_like.coe_injective,
  map_zero := map_zero,
  .. hF }

@[priority 100] -- See note [lower instance priority]
instance (F R A B : Type*) [comm_semiring R] [semiring A] [algebra R A] [has_star A]
  [semiring B] [algebra R B] [has_star B] [hF : star_alg_equiv_class F R A B] :
  star_alg_hom_class F R A B :=
{ coe := λ f, f,
  coe_injective' := fun_like.coe_injective,
  map_one := map_one,
  map_zero := map_zero,
  commutes := λ f r, by simp only [algebra.algebra_map_eq_smul_one, map_smul, map_one],
  .. hF}

end star_alg_equiv_class

namespace star_alg_equiv

section basic

variables {F R A B C : Type*}
  [has_add A] [has_mul A] [has_smul R A] [has_star A]
  [has_add B] [has_mul B] [has_smul R B] [has_star B]
  [has_add C] [has_mul C] [has_smul R C] [has_star C]

instance : star_alg_equiv_class (A ≃⋆ₐ[R] B) R A B :=
{ coe := to_fun,
  inv := inv_fun,
  left_inv := left_inv,
  right_inv := right_inv,
  coe_injective' := λ f g h₁ h₂, by { cases f, cases g, congr' },
  map_mul := map_mul',
  map_add := map_add',
  map_star := map_star',
  map_smul := map_smul' }

/--  Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (A ≃⋆ₐ[R] B) (λ _, A → B) := ⟨star_alg_equiv.to_fun⟩

@[ext]
lemma ext {f g : A ≃⋆ₐ[R] B} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

lemma ext_iff {f g : A ≃⋆ₐ[R] B} : f = g ↔ ∀ a, f a = g a  := fun_like.ext_iff

/-- Star algebra equivalences are reflexive. -/
@[refl] def refl : A ≃⋆ₐ[R] A :=
{ map_smul' := λ r a, rfl, map_star' := λ a, rfl, ..ring_equiv.refl A }

instance : inhabited (A ≃⋆ₐ[R] A) := ⟨refl⟩

@[simp] lemma coe_refl : ⇑(refl : A ≃⋆ₐ[R] A) = id := rfl

/-- Star algebra equivalences are symmetric. -/
@[symm]
def symm (e : A ≃⋆ₐ[R] B) : B ≃⋆ₐ[R] A :=
{ map_star' := λ b, by simpa only [e.left_inv (star (e.inv_fun b)), e.right_inv b]
    using congr_arg e.inv_fun (e.map_star' (e.inv_fun b)).symm,
  map_smul' := λ r b, by simpa only [e.left_inv (r • e.inv_fun b), e.right_inv b]
    using congr_arg e.inv_fun (e.map_smul' r (e.inv_fun b)).symm,
  ..e.to_ring_equiv.symm, }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A ≃⋆ₐ[R] B) : B → A := e.symm

initialize_simps_projections star_alg_equiv (to_fun → apply, inv_fun → simps.symm_apply)

@[simp] lemma inv_fun_eq_symm {e : A ≃⋆ₐ[R] B} : e.inv_fun = e.symm := rfl

@[simp] lemma symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e :=
by { ext, refl, }

lemma symm_bijective : function.bijective (symm : (A ≃⋆ₐ[R] B) → (B ≃⋆ₐ[R] A)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : A ≃⋆ₐ[R] B) (f h₁ h₂ h₃ h₄ h₅ h₆) :
  (⟨f, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ : B ≃⋆ₐ[R] A) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] lemma symm_mk (f f') (h₁ h₂ h₃ h₄ h₅ h₆) :
  (⟨f, f', h₁, h₂, h₃, h₄, h₅, h₆⟩ : A ≃⋆ₐ[R] B).symm =
  { to_fun := f', inv_fun := f,
    ..(⟨f, f', h₁, h₂, h₃, h₄, h₅, h₆⟩ : A ≃⋆ₐ[R] B).symm } := rfl

@[simp] lemma refl_symm : (star_alg_equiv.refl : A ≃⋆ₐ[R] A).symm = star_alg_equiv.refl := rfl

-- should be a `simp` lemma, but causes a linter timeout
lemma to_ring_equiv_symm (f : A ≃⋆ₐ[R] B) : (f : A ≃+* B).symm = f.symm := rfl

@[simp] lemma symm_to_ring_equiv (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃+* A) = (e : A ≃+* B).symm := rfl

/-- Star algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
{ map_smul' := λ r a, show e₂.to_fun (e₁.to_fun (r • a)) = r • e₂.to_fun (e₁.to_fun a),
    by rw [e₁.map_smul', e₂.map_smul'],
  map_star' := λ a, show e₂.to_fun (e₁.to_fun (star a)) = star (e₂.to_fun (e₁.to_fun a)),
    by rw [e₁.map_star', e₂.map_star'],
  ..(e₁.to_ring_equiv.trans e₂.to_ring_equiv), }

@[simp] lemma apply_symm_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e (e.symm x) = x :=
  e.to_ring_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e.symm (e x) = x :=
  e.to_ring_equiv.symm_apply_apply

@[simp] lemma symm_trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

@[simp] lemma coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) :
  ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[simp] lemma trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

theorem left_inverse_symm (e : A ≃⋆ₐ[R] B) : function.left_inverse e.symm e := e.left_inv

theorem right_inverse_symm (e : A ≃⋆ₐ[R] B) : function.right_inverse e.symm e := e.right_inv

end basic

section bijective

variables {F G R A B : Type*} [monoid R]
variables [non_unital_non_assoc_semiring A] [distrib_mul_action R A] [has_star A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R B] [has_star B]
variables [hF : non_unital_star_alg_hom_class F R A B] [non_unital_star_alg_hom_class G R B A]
include hF

/-- If a (unital or non-unital) star algebra morphism has an inverse, it is an isomorphism of
star algebras. -/
@[simps] def of_star_alg_hom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) :
  A ≃⋆ₐ[R] B :=
{ to_fun    := f,
  inv_fun   := g,
  left_inv  := h₁,
  right_inv := h₂,
  map_add' := map_add f,
  map_mul' := map_mul f,
  map_smul' := map_smul f,
  map_star' := map_star f }

/-- Promote a bijective star algebra homomorphism to a star algebra equivalence. -/
noncomputable def of_bijective (f : F) (hf : function.bijective f) : A ≃⋆ₐ[R] B :=
{ to_fun := f,
  map_star' := map_star f,
  map_smul' := map_smul f,
  .. ring_equiv.of_bijective f (hf : function.bijective (f : A → B)), }

@[simp] lemma coe_of_bijective {f : F} (hf : function.bijective f) :
  (star_alg_equiv.of_bijective f hf : A → B) = f := rfl

lemma of_bijective_apply {f : F} (hf : function.bijective f) (a : A) :
  (star_alg_equiv.of_bijective f hf) a = f a := rfl

end bijective

end star_alg_equiv

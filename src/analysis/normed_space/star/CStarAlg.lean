/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.star.star_alg_hom
import analysis.normed_space.star.basic
import analysis.complex.basic
import category_theory.elementwise
import category_theory.concrete_category.reflects_isomorphisms
import algebra.category.Algebra.basic

.

/-!
# Category instances for C⋆-algebras.

We introduce the bundled categories:
* `CStarAlg`
* `CStarAlg₁`
* `CommCStarAlg` -- actually we have to hold off on this
* `CommCStarAlg₁`
along with the relevant forgetful functors between them.
-/

section prerequisites

namespace non_unital_star_alg_hom

variables {F R A B : Type*} [monoid R] [has_star A] [has_star B] [non_unital_non_assoc_semiring A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R A] [distrib_mul_action R B]
variables [non_unital_star_alg_hom_class F R A B]

instance  : has_coe_t F (A →⋆ₙₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_smul' := map_smul f,
    map_zero' := map_zero f,
    map_add' := map_add f,
    map_mul' := map_mul f,
    map_star' := map_star f } }

@[simp, protected] lemma coe_coe (f : F) : ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

end non_unital_star_alg_hom

namespace star_alg_hom
variables {F R A B : Type*} [comm_semiring R] [semiring A] [algebra R A] [has_star A] [semiring B]
variables [algebra R B] [has_star B] [star_alg_hom_class F R A B]

instance  : has_coe_t F (A →⋆ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_one' := map_one f,
    commutes' := alg_hom_class.commutes f,
    ..(f : A →⋆ₙₐ[R] B) } }

@[simp, protected] lemma coe_coe (f : F) : ⇑(f : A →⋆ₐ[R] B) = f := rfl

end star_alg_hom

end prerequisites


universes u v

open category_theory

/-- The type of C⋆-algebras with ⋆-algebra morphisms. -/
structure CStarAlg :=
(α : Type u)
[is_non_unital_normed_ring : non_unital_normed_ring α]
[is_star_ring : star_ring α]
[is_cstar_ring : cstar_ring α]
[is_normed_space : normed_space ℂ α]
[is_is_scalar_tower : is_scalar_tower ℂ α α]
[is_smul_comm_class : smul_comm_class ℂ α α]
[is_star_module : star_module ℂ α]
[is_complete_space : complete_space α]

/-- The type of unital C⋆-algebras with unital ⋆-algebra morphisms. -/
structure CStarAlg₁ :=
(α : Type u)
[is_normed_ring : normed_ring α]
[is_star_ring : star_ring α]
[is_cstar_ring : cstar_ring α]
[is_normed_algebra : normed_algebra ℂ α]
[is_star_module : star_module ℂ α]
[is_complete_space : complete_space α]

/-
/-- The type of commutative C⋆-algebras with ⋆-algebra morphisms. -/
structure CommCStarAlg :=
(α : Type u)
[is_non_unital_normed_comm_ring : non_unital_normed_comm_ring α]
[is_star_ring : star_ring α]
[is_cstar_ring : cstar_ring α]
[is_normed_space : normed_space ℂ α]
[is_is_scalar_tower : is_scalar_tower ℂ α α]
[is_smul_comm_class : smul_comm_class ℂ α α]
[is_star_module : star_module ℂ α]
[is_complete_space : complete_space α]
-/

/-- The type of commutative unital C⋆-algebras with unital ⋆-algebra morphisms. -/
structure CommCStarAlg₁ :=
(α : Type u)
[is_normed_comm_ring : normed_comm_ring α]
[is_star_ring : star_ring α]
[is_cstar_ring : cstar_ring α]
[is_normed_algebra : normed_algebra ℂ α]
[is_star_module : star_module ℂ α]
[is_complete_space : complete_space α]

namespace CStarAlg

noncomputable instance : inhabited CStarAlg := ⟨⟨ℂ⟩⟩

instance : has_coe_to_sort CStarAlg (Type u) := ⟨CStarAlg.α⟩

attribute [instance] is_non_unital_normed_ring is_star_ring is_cstar_ring is_normed_space
  is_is_scalar_tower is_smul_comm_class is_star_module is_complete_space

noncomputable instance : category CStarAlg.{u} :=
{ hom := λ A B, A →⋆ₙₐ[ℂ] B,
  id := λ A, non_unital_star_alg_hom.id ℂ A,
  comp := λ A B C f g, g.comp f }

noncomputable instance : concrete_category CStarAlg.{u} :=
{ forget := { obj := λ A, A, map := λ A B f, f },
  forget_faithful := { } }

/-- Construct a bundled `CStarAlg` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [non_unital_normed_ring A] [star_ring A] [cstar_ring A] [normed_space ℂ A]
  [is_scalar_tower ℂ A A] [smul_comm_class ℂ A A] [star_module ℂ A] [complete_space A] :
  CStarAlg := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [non_unital_normed_ring A] [star_ring A] [cstar_ring A]
  [normed_space ℂ A] [is_scalar_tower ℂ A A] [smul_comm_class ℂ A A] [star_module ℂ A]
  [complete_space A] : (of A : Type u) = A := rfl

instance forget_non_unital_normed_ring (A : CStarAlg) :
  non_unital_normed_ring ((forget CStarAlg).obj A) :=
A.is_non_unital_normed_ring
instance forget_star_ring (A : CStarAlg) : star_ring ((forget CStarAlg).obj A) :=
A.is_star_ring
instance forget_cstar_ring (A : CStarAlg) : cstar_ring ((forget CStarAlg).obj A) :=
A.is_cstar_ring
instance forget_normed_space (A : CStarAlg) : normed_space ℂ ((forget CStarAlg).obj A) :=
A.is_normed_space
instance forget_is_scalar_tower (A : CStarAlg) :
  is_scalar_tower ℂ ((forget CStarAlg).obj A) ((forget CStarAlg).obj A) := A.is_is_scalar_tower
instance forget_is_smul_comm_class (A : CStarAlg) :
  smul_comm_class ℂ ((forget CStarAlg).obj A) ((forget CStarAlg).obj A) := A.is_smul_comm_class
instance forget_star_module (A : CStarAlg) : star_module ℂ ((forget CStarAlg).obj A) :=
A.is_star_module
instance forget_complete_space (A : CStarAlg) : complete_space ((forget CStarAlg).obj A) :=
A.is_complete_space

end CStarAlg

namespace CStarAlg₁

noncomputable instance : inhabited CStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : has_coe_to_sort CStarAlg₁ Type* := ⟨CStarAlg₁.α⟩

attribute [instance] is_normed_ring is_star_ring is_cstar_ring is_normed_algebra is_star_module
  is_complete_space

noncomputable instance : category CStarAlg₁.{u} :=
{ hom := λ A B, A →⋆ₐ[ℂ] B,
  id := λ A, star_alg_hom.id ℂ A,
  comp := λ A B C f g, g.comp f }

noncomputable instance : concrete_category CStarAlg₁.{u} :=
{ forget := { obj := λ A, A, map := λ A B f, f },
  forget_faithful := { } }

/-- Construct a bundled `CStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [normed_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : CStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [normed_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : (of A : Type u) = A := rfl

noncomputable instance has_forget_to_CStarAlg : has_forget₂ CStarAlg₁ CStarAlg :=
{ forget₂ :=
  { obj := λ A, ⟨A⟩,
    map := λ A B f, (f : A →⋆ₙₐ[ℂ] B), } }

noncomputable instance has_forget_to_Algebra : has_forget₂ CStarAlg₁ (Algebra ℂ) :=
{ forget₂ :=
  { obj := λ A, ⟨A⟩,
    map := λ A B f, f.to_alg_hom } }

/- need more imports for this, and probably we can get stronger statements, like `lipschitz_with 1`
Any morphism of `CStarAlg₁` is continuous.
lemma iso_of_bijective {X Y : CStarAlg₁.{u}} (f : X ⟶ Y) : continuous f :=
map_continuous (f : X →⋆ₐ[ℂ] Y) -/

end CStarAlg₁

namespace CommCStarAlg₁

noncomputable instance : inhabited CommCStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : has_coe_to_sort CommCStarAlg₁ Type* := ⟨CommCStarAlg₁.α⟩

attribute [instance] is_normed_comm_ring is_star_ring is_cstar_ring is_normed_algebra is_star_module
  is_complete_space

noncomputable instance : category CommCStarAlg₁.{u} :=
{ hom := λ A B, A →⋆ₐ[ℂ] B,
  id := λ A, star_alg_hom.id ℂ A,
  comp := λ A B C f g, g.comp f }

noncomputable instance : concrete_category CommCStarAlg₁.{u} :=
{ forget := { obj := λ A, A, map := λ A B f, f },
  forget_faithful := { } }

/-- Construct a bundled `CommCStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [normed_comm_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : CommCStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [normed_comm_ring A] [star_ring A] [cstar_ring A]
  [normed_algebra ℂ A] [star_module ℂ A] [complete_space A] : (of A : Type u) = A := rfl

instance has_forget_to_CStarAlg₁ : has_forget₂ CommCStarAlg₁ CStarAlg₁ :=
{ forget₂ :=
  { obj := λ A, ⟨A⟩,
    map := λ A B f, f } }

/- need more imports for this, and probably we can get stronger statements, like `lipschitz_with 1`
Any morphism of `CStarAlg₁` is continuous.
lemma iso_of_bijective {X Y : CStarAlg₁.{u}} (f : X ⟶ Y) : continuous f :=
map_continuous (f : X →⋆ₐ[ℂ] Y) -/

end CommCStarAlg₁

namespace star_alg_equiv

/-- Build an isomorphism in the category `CStarAlg` from a `star_alg_equiv` between C⋆-algebras -/
@[simps]
noncomputable def to_CStarAlg_iso {A B : Type u} [non_unital_normed_ring A] [star_ring A]
  [cstar_ring A] [normed_space ℂ A] [is_scalar_tower ℂ A A] [smul_comm_class ℂ A A]
  [star_module ℂ A] [complete_space A] [non_unital_normed_ring B] [star_ring B] [cstar_ring B]
  [normed_space ℂ B] [is_scalar_tower ℂ B B] [smul_comm_class ℂ B B] [star_module ℂ B]
  [complete_space B] (e : A ≃⋆ₐ[ℂ] B) : CStarAlg.of A ≅ CStarAlg.of B :=
{ hom := (e : A →⋆ₙₐ[ℂ] B),
  inv := (e.symm : B →⋆ₙₐ[ℂ] A),
  hom_inv_id' := non_unital_star_alg_hom.ext $ λ _, e.symm_apply_apply _,
  inv_hom_id' := non_unital_star_alg_hom.ext $ λ _, e.apply_symm_apply _ }

/-- Build an isomorphism in the category `CStarAlg₁` from a `star_alg_equiv` between unital
C⋆-algebras -/
@[simps]
noncomputable def to_CStarAlg₁_iso {A B : Type u} [normed_ring A] [star_ring A] [cstar_ring A]
  [normed_algebra ℂ A] [star_module ℂ A] [complete_space A] [normed_ring B] [star_ring B]
  [cstar_ring B] [normed_algebra ℂ B] [star_module ℂ B] [complete_space B]
  (e : A ≃⋆ₐ[ℂ] B) : CStarAlg₁.of A ≅ CStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id' := star_alg_hom.ext $ λ _, e.symm_apply_apply _,
  inv_hom_id' := star_alg_hom.ext $ λ _, e.apply_symm_apply _ }

/-- Build an isomorphism in the category `CommCStarAlg₁` from a `star_alg_equiv` between
commutative unital C⋆-algebras -/
@[simps]
noncomputable def to_CommCStarAlg₁_iso {A B : Type u} [normed_comm_ring A] [star_ring A]
  [cstar_ring A] [normed_algebra ℂ A] [star_module ℂ A] [complete_space A] [normed_comm_ring B]
  [star_ring B] [cstar_ring B] [normed_algebra ℂ B] [star_module ℂ B] [complete_space B]
  (e : A ≃⋆ₐ[ℂ] B) : CommCStarAlg₁.of A ≅ CommCStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id' := star_alg_hom.ext $ λ _, e.symm_apply_apply _,
  inv_hom_id' := star_alg_hom.ext $ λ _, e.apply_symm_apply _ }

end star_alg_equiv

namespace category_theory.iso

/-- Build a `star_alg_equiv` from an isomorphism in the category `CStarAlg`. -/
noncomputable def CStarAlg_iso_to_star_alg_equiv {X Y : CStarAlg} (i : X ≅ Y) : X ≃⋆ₐ[ℂ] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

/-- Build a `star_alg_equiv` from an isomorphism in the category `CStarAlg₁`. -/
noncomputable def CStarAlg₁_iso_to_star_alg_equiv {X Y : CStarAlg₁} (i : X ≅ Y) : X ≃⋆ₐ[ℂ] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

/-- Build a `star_alg_equiv` from an isomorphism in the category `CommCStarAlg₁`. -/
noncomputable def CommCStarAlg₁_iso_to_star_alg_equiv {X Y : CommCStarAlg₁} (i : X ≅ Y) :
  X ≃⋆ₐ[ℂ] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := i.hom_inv_id_apply,
  right_inv := i.inv_hom_id_apply,
  map_add'  := map_add i.hom,
  map_mul'  := map_mul i.hom,
  map_smul' := map_smul i.hom,
  map_star' := map_star i.hom, }

end category_theory.iso

instance CStarAlg.forget_reflects_isos : reflects_isomorphisms (forget CStarAlg.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CStarAlg).map f),
    let e : X ≃⋆ₐ[ℂ] Y := { ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CStarAlg_iso).1⟩,
  end }

instance CStarAlg₁.forget_reflects_isos : reflects_isomorphisms (forget CStarAlg₁.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CStarAlg₁).map f),
    let e : X ≃⋆ₐ[ℂ] Y := { map_smul' := map_smul f, ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CStarAlg₁_iso).1⟩,
  end }

instance CommCStarAlg₁.forget_reflects_isos : reflects_isomorphisms (forget CommCStarAlg₁.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    let i := as_iso ((forget CommCStarAlg₁).map f),
    let e : X ≃⋆ₐ[ℂ] Y := { map_smul' := map_smul f, ..f, ..i.to_equiv },
    exact ⟨(is_iso.of_iso e.to_CommCStarAlg₁_iso).1⟩,
  end }

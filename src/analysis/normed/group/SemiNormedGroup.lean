/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
import analysis.normed.group.hom
import category_theory.limits.shapes.zero_morphisms
import category_theory.concrete_category.bundled_hom
import category_theory.elementwise

/-!
# The category of seminormed groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup₁`, the subcategory of norm non-increasing morphisms.
-/

noncomputable theory

universes u

open category_theory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroup : Type (u+1) := bundled seminormed_add_comm_group

namespace SemiNormedGroup

instance bundled_hom : bundled_hom @normed_add_group_hom :=
⟨@normed_add_group_hom.to_fun, @normed_add_group_hom.id, @normed_add_group_hom.comp,
  @normed_add_group_hom.coe_inj⟩

attribute [derive [large_category, concrete_category]] SemiNormedGroup

instance : has_coe_to_sort SemiNormedGroup (Type u) := bundled.has_coe_to_sort

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [seminormed_add_comm_group M] : SemiNormedGroup := bundled.of M

instance (M : SemiNormedGroup) : seminormed_add_comm_group M := M.str

@[simp] lemma coe_of (V : Type u) [seminormed_add_comm_group V] :
  (SemiNormedGroup.of V : Type u) = V := rfl
@[simp] lemma coe_id (V : SemiNormedGroup) : ⇑(𝟙 V) = id := rfl
@[simp] lemma coe_comp {M N K : SemiNormedGroup} (f : M ⟶ N) (g : N ⟶ K) :
  ((f ≫ g) : M → K) = g ∘ f := rfl

instance : inhabited SemiNormedGroup := ⟨of punit⟩

instance of_unique (V : Type u) [seminormed_add_comm_group V] [i : unique V] :
  unique (SemiNormedGroup.of V) := i

instance : limits.has_zero_morphisms.{u (u+1)} SemiNormedGroup := {}

@[simp] lemma zero_apply {V W : SemiNormedGroup} (x : V) : (0 : V ⟶ W) x = 0 := rfl

lemma is_zero_of_subsingleton (V : SemiNormedGroup) [subsingleton V] :
  limits.is_zero V :=
begin
  refine ⟨λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩⟩,
  { ext, have : x = 0 := subsingleton.elim _ _, simp only [this, map_zero], },
  { ext, apply subsingleton.elim }
end

instance has_zero_object : limits.has_zero_object SemiNormedGroup.{u} :=
⟨⟨of punit, is_zero_of_subsingleton _⟩⟩

lemma iso_isometry_of_norm_noninc {V W : SemiNormedGroup} (i : V ≅ W)
  (h1 : i.hom.norm_noninc) (h2 : i.inv.norm_noninc) :
  isometry i.hom :=
begin
  apply add_monoid_hom_class.isometry_of_norm,
  intro v,
  apply le_antisymm (h1 v),
  calc ‖v‖ = ‖i.inv (i.hom v)‖ : by rw [iso.hom_inv_id_apply]
  ... ≤ ‖i.hom v‖ : h2 _,
end

end SemiNormedGroup

/--
`SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroup₁ : Type (u+1) := bundled seminormed_add_comm_group

namespace SemiNormedGroup₁

instance : has_coe_to_sort SemiNormedGroup₁ (Type u) := bundled.has_coe_to_sort

instance : large_category.{u} SemiNormedGroup₁ :=
{ hom := λ X Y, { f : normed_add_group_hom X Y // f.norm_noninc },
  id := λ X, ⟨normed_add_group_hom.id X, normed_add_group_hom.norm_noninc.id⟩,
  comp := λ X Y Z f g,
    ⟨(g : normed_add_group_hom Y Z).comp (f : normed_add_group_hom X Y), g.2.comp f.2⟩ }

@[ext] lemma hom_ext {M N : SemiNormedGroup₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
  f = g :=
subtype.eq (normed_add_group_hom.ext (congr_fun w))

instance : concrete_category.{u} SemiNormedGroup₁ :=
{ forget :=
  { obj := λ X, X,
    map := λ X Y f, f, },
  forget_faithful := {} }

/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [seminormed_add_comm_group M] : SemiNormedGroup₁ := bundled.of M

instance (M : SemiNormedGroup₁) : seminormed_add_comm_group M := M.str

/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mk_hom {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.norm_noninc) :
  SemiNormedGroup₁.of M ⟶ SemiNormedGroup₁.of N :=
⟨f, i⟩

@[simp] lemma mk_hom_apply {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.norm_noninc) (x) :
  mk_hom f i x = f x := rfl

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mk_iso {M N : SemiNormedGroup} (f : M ≅ N) (i : f.hom.norm_noninc) (i' : f.inv.norm_noninc) :
  SemiNormedGroup₁.of M ≅ SemiNormedGroup₁.of N :=
{ hom := mk_hom f.hom i,
  inv := mk_hom f.inv i',
  hom_inv_id' := by { apply subtype.eq, exact f.hom_inv_id, },
  inv_hom_id' := by { apply subtype.eq, exact f.inv_hom_id, }, }

instance : has_forget₂ SemiNormedGroup₁ SemiNormedGroup :=
{ forget₂ :=
  { obj := λ X, X,
    map := λ X Y f, f.1, }, }

@[simp] lemma coe_of (V : Type u) [seminormed_add_comm_group V] :
  (SemiNormedGroup₁.of V : Type u) = V := rfl
@[simp] lemma coe_id (V : SemiNormedGroup₁) : ⇑(𝟙 V) = id := rfl
@[simp] lemma coe_comp {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) :
  ((f ≫ g) : M → K) = g ∘ f := rfl
-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp] lemma coe_comp' {M N K : SemiNormedGroup₁} (f : M ⟶ N) (g : N ⟶ K) :
  ((f ≫ g) : normed_add_group_hom M K) = (↑g : normed_add_group_hom N K).comp ↑f := rfl

instance : inhabited SemiNormedGroup₁ := ⟨of punit⟩

instance of_unique (V : Type u) [seminormed_add_comm_group V] [i : unique V] :
  unique (SemiNormedGroup₁.of V) := i

instance : limits.has_zero_morphisms.{u (u+1)} SemiNormedGroup₁ :=
{ has_zero := λ X Y, { zero := ⟨0, normed_add_group_hom.norm_noninc.zero⟩, },
  comp_zero' := λ X Y f Z, by { ext, refl, },
  zero_comp' := λ X Y Z f, by { ext, simp [coe_fn_coe_base'] } }

@[simp] lemma zero_apply {V W : SemiNormedGroup₁} (x : V) : (0 : V ⟶ W) x = 0 := rfl

lemma is_zero_of_subsingleton (V : SemiNormedGroup₁) [subsingleton V] :
  limits.is_zero V :=
begin
  refine ⟨λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩⟩,
  { ext, have : x = 0 := subsingleton.elim _ _, simp only [this, map_zero],
    exact map_zero f.1 },
  { ext, apply subsingleton.elim }
end

instance has_zero_object : limits.has_zero_object SemiNormedGroup₁.{u} :=
⟨⟨of punit, is_zero_of_subsingleton _⟩⟩

lemma iso_isometry {V W : SemiNormedGroup₁} (i : V ≅ W) :
  isometry i.hom :=
begin
  change isometry (i.hom : V →+ W),
  refine add_monoid_hom_class.isometry_of_norm i.hom _,
  intro v,
  apply le_antisymm (i.hom.2 v),
  calc ‖v‖ = ‖i.inv (i.hom v)‖ : by rw [iso.hom_inv_id_apply]
      ... ≤ ‖i.hom v‖ : i.inv.2 _,
end

end SemiNormedGroup₁

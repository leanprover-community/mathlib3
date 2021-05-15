/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
import analysis.normed_space.normed_group_hom
import category_theory.concrete_category.bundled_hom
import category_theory.limits.shapes.zero

/-!
# The category of seminormed groups

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup'`, the subcategory of norm non-increasing morphisms.
-/

noncomputable theory

universes u

open category_theory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroup : Type (u+1) := bundled semi_normed_group

namespace SemiNormedGroup

instance bundled_hom : bundled_hom @normed_group_hom :=
⟨@normed_group_hom.to_fun, @normed_group_hom.id, @normed_group_hom.comp, @normed_group_hom.coe_inj⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] SemiNormedGroup

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [semi_normed_group M] : SemiNormedGroup := bundled.of M

instance (M : SemiNormedGroup) : semi_normed_group M := M.str

@[simp] lemma coe_of (V : Type u) [semi_normed_group V] : (SemiNormedGroup.of V : Type u) = V := rfl
@[simp] lemma coe_id (V : SemiNormedGroup) : ⇑(𝟙 V) = id := rfl

instance : has_zero SemiNormedGroup := ⟨of punit⟩
instance : inhabited SemiNormedGroup := ⟨0⟩

instance : limits.has_zero_morphisms SemiNormedGroup := {}

end SemiNormedGroup

/--
`SemiNormedGroup'` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
@[derive has_coe_to_sort]
def SemiNormedGroup' : Type (u+1) := bundled semi_normed_group

namespace SemiNormedGroup'

instance : large_category.{u} SemiNormedGroup' :=
{ hom := λ X Y, { f : normed_group_hom X Y // f.norm_noninc },
  id := λ X, ⟨normed_group_hom.id, normed_group_hom.norm_noninc.id⟩,
  comp := λ X Y Z f g, ⟨g.1.comp f.1, g.2.comp f.2⟩, }

@[ext] lemma hom_ext {M N : SemiNormedGroup'} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
  f = g :=
subtype.eq (normed_group_hom.ext (congr_fun w))

instance : concrete_category.{u} SemiNormedGroup' :=
{ forget :=
  { obj := λ X, X,
    map := λ X Y f, f, },
  forget_faithful := {} }

/-- Construct a bundled `SemiNormedGroup'` from the underlying type and typeclass. -/
def of (M : Type u) [semi_normed_group M] : SemiNormedGroup' := bundled.of M

instance (M : SemiNormedGroup') : semi_normed_group M := M.str

/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup'`. -/
def mk_hom {M N : SemiNormedGroup} (f : M ⟶ N) (i : f.norm_noninc) :
  SemiNormedGroup'.of M ⟶ SemiNormedGroup'.of N :=
⟨f, i⟩

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup'`. -/
def mk_iso {M N : SemiNormedGroup} (f : M ≅ N) (i : f.hom.norm_noninc) (i' : f.inv.norm_noninc) :
  SemiNormedGroup'.of M ≅ SemiNormedGroup'.of N :=
{ hom := mk_hom f.hom i,
  inv := mk_hom f.inv i',
  hom_inv_id' := by { apply subtype.eq, exact f.hom_inv_id, },
  inv_hom_id' := by { apply subtype.eq, exact f.inv_hom_id, }, }

instance : has_forget₂ SemiNormedGroup' SemiNormedGroup :=
{ forget₂ :=
  { obj := λ X, X,
    map := λ X Y f, f.1, }, }

@[simp] lemma coe_of (V : Type u) [semi_normed_group V] : (SemiNormedGroup'.of V : Type u) = V :=
rfl
@[simp] lemma coe_id (V : SemiNormedGroup') : ⇑(𝟙 V) = id := rfl
@[simp] lemma coe_comp {M N K : SemiNormedGroup'} (f : M ⟶ N) (g : N ⟶ K) :
  ((f ≫ g) : M → K) = g ∘ f := rfl

instance : has_zero SemiNormedGroup' := ⟨of punit⟩
instance : inhabited SemiNormedGroup' := ⟨0⟩

instance : limits.has_zero_morphisms SemiNormedGroup' :=
{ has_zero := λ X Y, { zero := ⟨0, normed_group_hom.norm_noninc.zero⟩, },
  comp_zero' := λ X Y f Z, by { ext, refl, },
  zero_comp' := λ X Y Z f, by { ext, simp, }, }

lemma iso_isometry {V W : SemiNormedGroup'} (i : V ≅ W) :
  isometry i.hom :=
begin
  apply normed_group_hom.isometry_of_norm,
  intro v,
  apply le_antisymm (i.hom.2 v),
  calc ∥v∥ = ∥i.inv (i.hom v)∥ : by rw [coe_hom_inv_id]
      ... ≤ ∥i.hom v∥ : i.inv.2 _,
end

end SemiNormedGroup'

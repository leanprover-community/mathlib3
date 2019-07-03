/- Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison

Introduce UniformSpace -- the category of uniform spaces.
-/
import category_theory.concrete_category
import category_theory.full_subcategory
import category_theory.adjunction.basic
import topology.uniform_space.completion
import topology.Top.basic

universes u v

open category_theory

/-- The category of uniform spaces. -/
@[reducible] def UniformSpace : Type (u+1) := bundled uniform_space

namespace UniformSpace

instance (x : UniformSpace) : uniform_space x := x.str

-- TODO fix the order of the implicit arguments f and g in uniform_continuous.comp,
-- then replace the second half of this with `@uniform_continuous.comp`.
instance concrete_category_uniform_continuous : concrete_category @uniform_continuous :=
⟨@uniform_continuous_id, by { introsI, apply uniform_continuous.comp; assumption }⟩

def of (α : Type u) [uniform_space α] : UniformSpace := ⟨α⟩

abbreviation forget : UniformSpace.{u} ⥤ Type u := forget

instance forget.faithful : faithful (forget) := {}

def forget_to_Top : UniformSpace.{u} ⥤ Top.{u} :=
{ obj := λ X, { α := X.1 },
  map := λ X Y f, ⟨ f, uniform_continuous.continuous f.property ⟩ }

def forget_to_Type_via_Top : forget_to_Top ⋙ Top.forget ≅ forget := iso.refl _

end UniformSpace

structure CpltSepUniformSpace :=
(α : Type u)
[is_uniform_space : uniform_space α]
[is_complete_space : complete_space α]
[is_separated : separated α]

namespace CpltSepUniformSpace

instance : has_coe_to_sort CpltSepUniformSpace :=
{ S := Type u, coe := CpltSepUniformSpace.α }

attribute [instance] is_uniform_space is_complete_space is_separated

def to_UniformSpace (X : CpltSepUniformSpace) : UniformSpace :=
⟨X⟩

instance (X : CpltSepUniformSpace) : complete_space ((to_UniformSpace X).α) := CpltSepUniformSpace.is_complete_space X
instance (X : CpltSepUniformSpace) : separated ((to_UniformSpace X).α) := CpltSepUniformSpace.is_separated X

instance CpltSepUniformSpace_category : category CpltSepUniformSpace :=
induced_category.category to_UniformSpace

def of (X : Type u) [uniform_space X] [complete_space X] [separated X] : CpltSepUniformSpace := ⟨X⟩

def forget_to_UniformSpace : CpltSepUniformSpace ⥤ UniformSpace := induced_functor to_UniformSpace

def forget : CpltSepUniformSpace ⥤ Type u :=
{ obj := λ R, R,
  map := λ R S f, f.1 }

instance forget_faithful : faithful forget := {}
instance forget_to_UniformSpace_full : full forget_to_UniformSpace :=
induced_category.full _
instance forget_to_UniformSpace_faithful : faithful forget_to_UniformSpace :=
induced_category.faithful _

def forget_to_Type_via_UniformSpace : forget_to_UniformSpace ⋙ UniformSpace.forget ≅ forget := iso.refl _

end CpltSepUniformSpace

namespace UniformSpace

open uniform_space
open CpltSepUniformSpace

noncomputable def completion_functor : UniformSpace ⥤ CpltSepUniformSpace :=
{ obj := λ X, CpltSepUniformSpace.of (completion X),
  map := λ X Y f, ⟨completion.map f.1, completion.uniform_continuous_map⟩,
  map_comp' := λ X Y Z f g,
  begin cases f, cases g, apply subtype.ext.2, dsimp, rw ←completion.map_comp; assumption end }.

def completion_hom (X : UniformSpace) : X ⟶ forget_to_UniformSpace.obj (completion_functor.obj X) :=
{ val := (coe : X → completion X),
  property := completion.uniform_continuous_coe X }

@[simp] lemma completion_hom_val (X : UniformSpace) (x) :
  (completion_hom X) x = (x : completion X) := rfl

noncomputable def extension_hom {X : UniformSpace} {Y : CpltSepUniformSpace} (f : X ⟶ forget_to_UniformSpace.obj Y) :
  completion_functor.obj X ⟶ Y :=
{ val := completion.extension f,
  property := completion.uniform_continuous_extension }

@[simp] lemma extension_hom_val {X : UniformSpace} {Y : CpltSepUniformSpace}
  (f : X ⟶ forget_to_UniformSpace.obj Y) (x) :
  (extension_hom f) x = completion.extension f x := rfl.

@[simp] lemma extension_comp_coe {X : UniformSpace} {Y : CpltSepUniformSpace}
(f : to_UniformSpace (CpltSepUniformSpace.of (completion X)) ⟶ to_UniformSpace Y) :
extension_hom (completion_hom X ≫ f) = f :=
by { ext x, exact congr_fun (completion.extension_comp_coe f.property) x }

-- @[extensionality] lemma foo {X : UniformSpace} {Y : CpltSepUniformSpace} (f g : completion_functor.obj X ⟶ Y)
--   (h : completion_hom X ≫ (forget_to_UniformSpace.map f) = completion_hom X ≫ (forget_to_UniformSpace.map g)) : f = g :=
-- begin
--   sorry
-- end

-- TODO once someone does reflexive subcategories, perhaps update this:
noncomputable def adj : completion_functor ⊣ forget_to_UniformSpace :=
adjunction.mk_of_hom_equiv
-- begin end
-- { hom_equiv := begin end }
begin
  fsplit, intros, fsplit,
  { intro f, exact completion_hom X ≫ f, },
  { intro f, exact extension_hom f, },
  { intro f, simp },
  { intro f, ext1, cases f, dsimp, erw completion.extension_coe, assumption },
  { dsimp, intros X X' Y f g, ext1, dsimp, erw ←completion.extension_map,refl, exact g.property, exact f.property, },
  { intros X Y Y' f g, refl },
end

end UniformSpace

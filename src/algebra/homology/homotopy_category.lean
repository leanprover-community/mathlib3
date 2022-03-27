/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homotopy
import category_theory.quotient

/-!
# The homotopy category

`homotopy_category V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [preadditive V]
variables (c : complex_shape ι)

/--
The congruence on `homological_complex V c` given by the existence of a homotopy.
-/
def homotopic : hom_rel (homological_complex V c) := λ C D f g, nonempty (homotopy f g)

instance homotopy_congruence : congruence (homotopic V c) :=
{ is_equiv := λ C D,
  { refl := λ C, ⟨homotopy.refl C⟩,
    symm := λ f g ⟨w⟩, ⟨w.symm⟩,
    trans := λ f g h ⟨w₁⟩ ⟨w₂⟩, ⟨w₁.trans w₂⟩, },
  comp_left := λ E F G m₁ m₂ g ⟨i⟩, ⟨i.comp_left _⟩,
  comp_right := λ E F G f m₁ m₂ ⟨i⟩, ⟨i.comp_right _⟩, }

/-- `homotopy_category V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic. -/
@[derive category]
def homotopy_category := category_theory.quotient (homotopic V c)

-- TODO the homotopy_category is preadditive

namespace homotopy_category

/-- The quotient functor from complexes to the homotopy category. -/
def quotient : homological_complex V c ⥤ homotopy_category V c :=
category_theory.quotient.functor _

local attribute [instance] has_zero_object.has_zero

-- TODO upgrade this is to `has_zero_object`, presumably for any `quotient`.
instance [has_zero_object V] : inhabited (homotopy_category V c) := ⟨(quotient V c).obj 0⟩

variables {V c}

@[simp] lemma quotient_obj_as (C : homological_complex V c) :
  ((quotient V c).obj C).as = C := rfl

@[simp] lemma quotient_map_out {C D : homotopy_category V c} (f : C ⟶ D) :
  (quotient V c).map f.out = f :=
quot.out_eq _

lemma eq_of_homotopy {C D : homological_complex V c} (f g : C ⟶ D) (h : homotopy f g) :
  (quotient V c).map f = (quotient V c).map g :=
category_theory.quotient.sound _ ⟨h⟩

/-- If two chain maps become equal in the homotopy category, then they are homotopic. -/
def homotopy_of_eq {C D : homological_complex V c} (f g : C ⟶ D)
  (w : (quotient V c).map f = (quotient V c).map g) : homotopy f g :=
((quotient.functor_map_eq_iff _ _ _).mp w).some

/--
An arbitrarily chosen representation of the image of a chain map in the homotopy category
is homotopic to the original chain map.
-/
def homotopy_out_map {C D : homological_complex V c} (f : C ⟶ D) :
  homotopy ((quotient V c).map f).out f :=
begin
  apply homotopy_of_eq,
  simp,
end

@[simp] lemma quotient_map_out_comp_out {C D E : homotopy_category V c} (f : C ⟶ D) (g : D ⟶ E) :
  (quotient V c).map (quot.out f ≫ quot.out g) = f ≫ g :=
by conv_rhs { erw [←quotient_map_out f, ←quotient_map_out g, ←(quotient V c).map_comp], }

/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
def iso_of_homotopy_equiv {C D : homological_complex V c} (f : homotopy_equiv C D) :
  (quotient V c).obj C ≅ (quotient V c).obj D :=
{ hom := (quotient V c).map f.hom,
  inv := (quotient V c).map f.inv,
  hom_inv_id' := begin
    rw [←(quotient V c).map_comp, ←(quotient V c).map_id],
    exact eq_of_homotopy _ _ f.homotopy_hom_inv_id,
  end,
  inv_hom_id' := begin
    rw [←(quotient V c).map_comp, ←(quotient V c).map_id],
    exact eq_of_homotopy _ _ f.homotopy_inv_hom_id,
  end }

/-- If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent. -/
def homotopy_equiv_of_iso
  {C D : homological_complex V c} (i : (quotient V c).obj C ≅ (quotient V c).obj D) :
  homotopy_equiv C D :=
{ hom := quot.out i.hom,
  inv := quot.out i.inv,
  homotopy_hom_inv_id := homotopy_of_eq _ _ (by { simp, refl, }),
  homotopy_inv_hom_id := homotopy_of_eq _ _ (by { simp, refl, }), }

variables (V c) [has_zero_object V] [has_equalizers V] [has_images V] [has_image_maps V]
  [has_cokernels V]

/-- The `i`-th homology, as a functor from the homotopy category. -/
def homology_functor (i : ι) : homotopy_category V c ⥤ V :=
category_theory.quotient.lift _ (homology_functor V c i)
  (λ C D f g ⟨h⟩, homology_map_eq_of_homotopy h i)

/-- The homology functor on the homotopy category is just the usual homology functor. -/
def homology_factors (i : ι) :
  quotient V c ⋙ homology_functor V c i ≅ _root_.homology_functor V c i :=
category_theory.quotient.lift.is_lift _ _ _

@[simp] lemma homology_factors_hom_app (i : ι) (C : homological_complex V c) :
  (homology_factors V c i).hom.app C = 𝟙 _ :=
rfl

@[simp] lemma homology_factors_inv_app (i : ι) (C : homological_complex V c) :
  (homology_factors V c i).inv.app C = 𝟙 _ :=
rfl

lemma homology_functor_map_factors (i : ι) {C D : homological_complex V c} (f : C ⟶ D) :
  (_root_.homology_functor V c i).map f =
    ((homology_functor V c i).map ((quotient V c).map f) : _) :=
(category_theory.quotient.lift_map_functor_map _ (_root_.homology_functor V c i) _ f).symm

end homotopy_category

namespace category_theory

variables {V} {W : Type*} [category W] [preadditive W]

/-- An additive functor induces a functor between homotopy categories. -/
@[simps]
def functor.map_homotopy_category (c : complex_shape ι) (F : V ⥤ W) [F.additive] :
  homotopy_category V c ⥤ homotopy_category W c :=
{ obj := λ C, (homotopy_category.quotient W c).obj ((F.map_homological_complex c).obj C.as),
  map := λ C D f,
    (homotopy_category.quotient W c).map ((F.map_homological_complex c).map (quot.out f)),
  map_id' := λ C, begin
    rw ←(homotopy_category.quotient W c).map_id,
    apply homotopy_category.eq_of_homotopy,
    rw ←(F.map_homological_complex c).map_id,
    apply F.map_homotopy,
    apply homotopy_category.homotopy_of_eq,
    exact quot.out_eq _,
  end,
  map_comp' := λ C D E f g, begin
    rw ←(homotopy_category.quotient W c).map_comp,
    apply homotopy_category.eq_of_homotopy,
    rw ←(F.map_homological_complex c).map_comp,
    apply F.map_homotopy,
    apply homotopy_category.homotopy_of_eq,
    convert quot.out_eq _,
    exact homotopy_category.quotient_map_out_comp_out _ _,
  end }.

-- TODO `F.map_homotopy_category c` is additive (and linear when `F` is linear).

/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
def nat_trans.map_homotopy_category {F G : V ⥤ W} [F.additive] [G.additive]
  (α : F ⟶ G) (c : complex_shape ι) : F.map_homotopy_category c ⟶ G.map_homotopy_category c :=
{ app := λ C,
    (homotopy_category.quotient W c).map ((nat_trans.map_homological_complex α c).app C.as),
  naturality' := λ C D f,
  begin
    dsimp,
    simp only [←functor.map_comp],
    congr' 1,
    ext,
    dsimp,
    simp,
  end }

@[simp] lemma nat_trans.map_homotopy_category_id (c : complex_shape ι) (F : V ⥤ W) [F.additive] :
  nat_trans.map_homotopy_category (𝟙 F) c = 𝟙 (F.map_homotopy_category c) :=
by tidy

@[simp] lemma nat_trans.map_homotopy_category_comp (c : complex_shape ι)
  {F G H : V ⥤ W} [F.additive] [G.additive] [H.additive]
  (α : F ⟶ G) (β : G ⟶ H):
  nat_trans.map_homotopy_category (α ≫ β) c =
    nat_trans.map_homotopy_category α c ≫ nat_trans.map_homotopy_category β c :=
by tidy

end category_theory

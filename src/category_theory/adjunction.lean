/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/

import category_theory.limits.preserves
import category_theory.whiskering
import category_theory.equivalence

namespace category_theory
open category
open category_theory.limits

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

local attribute [elab_simple] whisker_left whisker_right

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

/--
`adjunction F G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π (X Y), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(unit : functor.id C ⟶ F.comp G)
(counit : G.comp F ⟶ functor.id D)
(hom_equiv_unit' : Π {X Y f}, (hom_equiv X Y) f = (unit : _ ⟹ _).app X ≫ G.map f . obviously)
(hom_equiv_counit' : Π {X Y g}, (hom_equiv X Y).symm g = F.map g ≫ counit.app Y . obviously)

namespace adjunction

restate_axiom hom_equiv_unit'
restate_axiom hom_equiv_counit'
attribute [simp, priority 1] hom_equiv_unit hom_equiv_counit

section

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction F G) {X' X : C} {Y Y' : D}

@[simp, priority 1] lemma hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
  (adj.hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.hom_equiv X Y).symm g :=
by rw [hom_equiv_counit, F.map_comp, assoc, adj.hom_equiv_counit.symm]

@[simp] lemma hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
  (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g :=
by rw [← equiv.eq_symm_apply]; simp [-hom_equiv_unit]

@[simp, priority 1] lemma hom_equiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y') (f ≫ g) = (adj.hom_equiv X Y) f ≫ G.map g :=
by rw [hom_equiv_unit, G.map_comp, ← assoc, ←hom_equiv_unit]

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g :=
by rw [equiv.symm_apply_eq]; simp [-hom_equiv_counit]

@[simp] lemma left_triangle :
  (whisker_right adj.unit F).vcomp (whisker_left F adj.counit) = nat_trans.id _ :=
begin
  ext1 X, dsimp,
  erw [← adj.hom_equiv_counit, equiv.symm_apply_eq, adj.hom_equiv_unit],
  simp
end

@[simp] lemma right_triangle :
  (whisker_left G adj.unit).vcomp (whisker_right adj.counit G) = nat_trans.id _ :=
begin
  ext1 Y, dsimp,
  erw [← adj.hom_equiv_unit, ← equiv.eq_symm_apply, adj.hom_equiv_counit],
  simp
end

@[simp] lemma left_triangle_components :
  F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ functor.id C ⋙ F), t.app X) adj.left_triangle

@[simp] lemma right_triangle_components {Y : D} :
  adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ G ⋙ functor.id C), t.app Y) adj.right_triangle

end

structure core_hom_equiv (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π (X Y), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(hom_equiv_naturality_left_symm' : Π {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
  (hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (hom_equiv X Y).symm g . obviously)
(hom_equiv_naturality_right' : Π {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
  (hom_equiv X Y') (f ≫ g) = (hom_equiv X Y) f ≫ G.map g . obviously)

namespace core_hom_equiv

restate_axiom hom_equiv_naturality_left_symm'
restate_axiom hom_equiv_naturality_right'
attribute [simp, priority 1] hom_equiv_naturality_left_symm hom_equiv_naturality_right

variables {F : C ⥤ D} {G : D ⥤ C} (adj : core_hom_equiv F G) {X' X : C} {Y Y' : D}

@[simp] lemma hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
  (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g :=
by rw [← equiv.eq_symm_apply]; simp

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g :=
by rw [equiv.symm_apply_eq]; simp

end core_hom_equiv

structure core_unit_counit (F : C ⥤ D) (G : D ⥤ C) :=
(unit : functor.id C ⟶ F.comp G)
(counit : G.comp F ⟶ functor.id D)
(left_triangle' : (whisker_right unit F).vcomp (whisker_left F counit) = nat_trans.id _ . obviously)
(right_triangle' : (whisker_left G unit).vcomp (whisker_right counit G) = nat_trans.id _ . obviously)

namespace core_unit_counit

restate_axiom left_triangle'
restate_axiom right_triangle'
attribute [simp] left_triangle right_triangle

end core_unit_counit

variables (F : C ⥤ D) (G : D ⥤ C)

def mk_of_hom_equiv (adj : core_hom_equiv F G) : adjunction F G :=
{ unit :=
  { app := λ X, (adj.hom_equiv X (F.obj X)) (𝟙 (F.obj X)),
    naturality' :=
    begin
      intros,
      erw [← adj.hom_equiv_naturality_left, ← adj.hom_equiv_naturality_right],
      dsimp, simp
    end },
  counit :=
  { app := λ Y, (adj.hom_equiv _ _).inv_fun (𝟙 (G.obj Y)),
    naturality' :=
    begin
      intros,
      erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm],
      dsimp, simp
    end },
  hom_equiv_unit' := λ X Y f, by erw [← adj.hom_equiv_naturality_right]; simp,
  hom_equiv_counit' := λ X Y f, by erw [← adj.hom_equiv_naturality_left_symm]; simp,
  .. adj }

def mk_of_unit_counit (adj : core_unit_counit F G) : adjunction F G :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, adj.unit.app X ≫ G.map f,
    inv_fun := λ g, F.map g ≫ adj.counit.app Y,
    left_inv := λ f, begin
      change F.map (_ ≫ _) ≫ _ = _,
      rw [F.map_comp, assoc, ←functor.comp_map, adj.counit.naturality, ←assoc],
      convert id_comp _ f,
      exact congr_arg (λ t : _ ⟹ _, t.app _) adj.left_triangle
    end,
    right_inv := λ g, begin
      change _ ≫ G.map (_ ≫ _) = _,
      rw [G.map_comp, ←assoc, ←functor.comp_map, ←adj.unit.naturality, assoc],
      convert comp_id _ g,
      exact congr_arg (λ t : _ ⟹ _, t.app _) adj.right_triangle
  end },
  .. adj }

section
omit 𝒟

def id : adjunction (functor.id C) (functor.id C) :=
{ hom_equiv := λ X Y, equiv.refl _,
  unit := 𝟙 _,
  counit := 𝟙 _ }

end

/-
TODO
* define adjoint equivalences
* show that every equivalence can be improved into an adjoint equivalence
-/

section
variables {E : Type u₃} [ℰ : category.{v₃} E] (H : D ⥤ E) (I : E ⥤ D)

def comp (adj₁ : adjunction F G) (adj₂ : adjunction H I) : adjunction (F ⋙ H) (I ⋙ G) :=
{ hom_equiv := λ X Z, equiv.trans (adj₂.hom_equiv _ _) (adj₁.hom_equiv _ _),
  unit := adj₁.unit ≫
  (whisker_left F $ whisker_right adj₂.unit G) ≫ (functor.associator _ _ _).inv,
  counit := (functor.associator _ _ _).hom ≫
    (whisker_left I $ whisker_right adj₁.counit H) ≫ adj₂.counit }

end

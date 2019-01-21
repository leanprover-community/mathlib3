/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/

import category_theory.limits.preserves
import category_theory.whiskering
import data.equiv.basic
import tactic.where

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
(hom_equiv_unit' : Π {X}, (hom_equiv X (F.obj X)) (𝟙 (F.obj X)) = (unit : _ ⟹ _).app X . obviously)
(hom_equiv_counit' : Π {Y}, (hom_equiv (G.obj Y) Y).symm (𝟙 (G.obj Y)) = counit.app Y . obviously)
(hom_equiv_naturality_left_symm' : Π {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
  (hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (hom_equiv X Y).symm g . obviously)
(hom_equiv_naturality_right' : Π {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
  (hom_equiv X Y') (f ≫ g) = (hom_equiv X Y) f ≫ G.map g . obviously)
(left_triangle' : (whisker_right unit F).vcomp (whisker_left F counit) = nat_trans.id _ . obviously)
(right_triangle' : (whisker_left G unit).vcomp (whisker_right counit G) = nat_trans.id _ . obviously)

namespace adjunction

restate_axiom hom_equiv_unit'
restate_axiom hom_equiv_counit'
restate_axiom hom_equiv_naturality_left_symm'
restate_axiom hom_equiv_naturality_right'
restate_axiom left_triangle'
restate_axiom right_triangle'

attribute [simp, priority 1] hom_equiv_unit hom_equiv_counit
attribute [simp, priority 1] hom_equiv_naturality_left_symm hom_equiv_naturality_right
attribute [simp] left_triangle right_triangle

section

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction F G) {X' X : C} {Y Y' : D}

@[simp] lemma left_triangle_components :
  F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ functor.id C ⋙ F), t.app X) adj.left_triangle

@[simp] lemma right_triangle_components {Y : D} :
  adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ G ⋙ functor.id C), t.app Y) adj.right_triangle

@[simp] lemma hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
  (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g :=
by rw [← equiv.eq_symm_apply]; simp

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g :=
by rw [equiv.symm_apply_eq]; simp

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
  left_triangle' :=
  begin
    ext1, dsimp,
    erw ← adj.hom_equiv_naturality_left_symm,
    simp,
  end,
  right_triangle' :=
  begin
    ext1, dsimp,
    erw ← adj.hom_equiv_naturality_right,
    simpa using (adj.hom_equiv _ _).right_inv (𝟙 _)
  end,
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
variables {E : Type u₃} [ℰ : category.{v₃} E] (H : D ⥤ E) (I : E ⥤ D)

def trans (adj₁ : adjunction F G) (adj₂ : adjunction H I) : adjunction (F ⋙ H) (I ⋙ G) :=
{ hom_equiv := λ X Z, equiv.trans (adj₂.hom_equiv _ _) (adj₁.hom_equiv _ _),
  unit := adj₁.unit ≫ begin
    refine whisker_left F (G.left_unitor.inv ≫ whisker_right adj₂.unit G) ≫ _,
    refine _ ≫ (functor.associator _ _ _).inv,
    exact whisker_left F (functor.associator _ _ _).hom
    end,
  counit :=
  { app := λ Z, _ } }


end

section construct_left
-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variables {F_obj : C → D} {G}
variables (e : Π X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
variables (he : Π X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
include he

private lemma he' {X Y Y'} (f g) : (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g :=
by intros; rw [equiv.symm_apply_eq, he]; simp

def left_adjoint_of_equiv : C ⥤ D :=
{ obj := F_obj,
  map := λ X X' f, (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _)),
  map_comp' := λ X X' X'' f f', begin
    rw [equiv.symm_apply_eq, he, equiv.apply_inverse_apply],
    conv { to_rhs, rw [assoc, ←he, id_comp, equiv.apply_inverse_apply] },
    simp
  end }

def adjunction_of_equiv_left : adjunction (left_adjoint_of_equiv e he) G :=
mk_of_hom_equiv (left_adjoint_of_equiv e he) G
{ hom_equiv := e,
  hom_equiv_naturality_left_symm' :=
  begin
    intros,
    erw [← he' e he, ← equiv.apply_eq_iff_eq],
    simp [(he _ _ _ _ _).symm]
  end }

end construct_left

section construct_right
-- Construction of a right adjoint, analogous to the above.
variables {F} {G_obj : D → C}
variables (e : Π X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))
variables (he : Π X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
include he

private lemma he' {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) :=
by intros; rw [equiv.eq_symm_apply, he]; simp

def right_adjoint_of_equiv : D ⥤ C :=
{ obj := G_obj,
  map := λ Y Y' g, (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g),
  map_comp' := λ Y Y' Y'' g g', begin
    rw [← equiv.eq_symm_apply, ← he' e he, equiv.inverse_apply_apply],
    conv { to_rhs, rw [← assoc, he' e he, comp_id, equiv.inverse_apply_apply] },
    simp
  end }

def adjunction_of_equiv_right : adjunction F (right_adjoint_of_equiv e he) :=
mk_of_hom_equiv F (right_adjoint_of_equiv e he)
{ hom_equiv := e,
  hom_equiv_naturality_left_symm' := by intros; rw [equiv.symm_apply_eq, he]; simp,
  hom_equiv_naturality_right' :=
  begin
    intros X Y Y' g h,
    erw [←he, equiv.apply_eq_iff_eq, ←assoc, he' e he, comp_id, equiv.inverse_apply_apply]
  end }

end construct_right

end adjunction

end category_theory

namespace category_theory.adjunction
open category_theory
open category_theory.functor
open category_theory.limits

universes u₁ u₂ v

variables {C : Type u₁} [𝒞 : category.{v} C] {D : Type u₂} [𝒟 : category.{v} D]
include 𝒞 𝒟

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction F G)
include adj

section preservation

@[simp] def foo {J : Type v} [small_category J] (K : J ⥤ C) : cocone (K ⋙ F) ⥤ cocone K :=
(cocones.functoriality G) ⋙  (cocones.precompose
  ((right_unitor _).inv ⊟ (whisker_left K adj.unit) ⊟ (associator _ _ _).inv))

def adjunction_of_foo {J : Type v} [small_category J] {K : J ⥤ C} :
  adjunction (cocones.functoriality F) (adj.foo K) :=
mk_of_unit_counit _ _
{ unit :=
  { app := λ c,
    { hom := adj.unit.app c.X,
      w' := λ j, by have := adj.unit.naturality (c.ι.app j); tidy },
    naturality' := λ _ _ f, by have := adj.unit.naturality (f.hom); tidy },
  counit :=
  { app := λ c,
    { hom := adj.counit.app c.X,
      w' :=
      begin
        intro j,
        dsimp,
        erw [category.comp_id, category.id_comp, F.map_comp, category.assoc,
          adj.counit.naturality (c.ι.app j), ← category.assoc, adj.left_triangle_components,
          category.id_comp],
        refl,
      end },
    naturality' := λ _ _ f, by have := adj.counit.naturality (f.hom); tidy },
    left_triangle'  := by { ext1 c, ext, dsimp, exact adj.left_triangle_components },
    right_triangle' := by { ext1 c, ext, dsimp, exact adj.right_triangle_components } }

/-- A left adjoint preserves colimits. -/
def left_adjoint_preserves_colimits : preserves_colimits F :=
λ J 𝒥 K, by resetI; exact
{ preserves := λ c hc, is_colimit_iso_unique_cocone_morphism.inv
    (λ s, ((adjunction_of_foo adj).hom_equiv _ _).unique_of_equiv $
      is_colimit_iso_unique_cocone_morphism.hom hc _ ) }

-- /-- A right adjoint preserves limits. -/
-- def right_adjoint_preserves_limits : preserves_limits G :=
-- ⟨λ J 𝒥, by exactI λ Y c h, limits.is_limit.of_equiv
--   (λ Z, calc
--      (Z ⟶ G.obj c.X) ≃ (F.obj Z ⟶ c.X)            : adj.hom_equiv.symm
--      ... ≃ ((functor.const J).obj (F.obj Z) ⟶ Y)  : (h.equiv (F.obj Z)).to_equiv
--      ... ≃ ((functor.const J).obj Z ⟶ Y.comp G)   : adj.cone_equiv)
--   (λ Z f j, begin
--      dsimp [is_limit.equiv, cone_equiv],
--      rw adj.hom_equiv_naturality,
--      erw adj.hom_equiv.right_inv f,
--      simp
--    end)⟩

end preservation

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
def cocones_iso {J : Type v} [small_category J] {K : J ⥤ C} :
  (cocones J D).obj (K ⋙ F) ≅ G ⋙ ((cocones J C).obj K) :=
nat_iso.of_components (λ Y,
{ hom := λ t,
    { app := λ j, (adj.hom_equiv (K.obj j) Y) (t.app j),
      naturality' := λ j j' f, by erw [← adj.hom_equiv_naturality_left, t.naturality]; dsimp; simp },
  inv := λ t,
    { app := λ j, (adj.hom_equiv (K.obj j) Y).symm (t.app j),
      naturality' := λ j j' f, begin
        erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm, t.naturality],
        dsimp, simp
      end } } )
begin
  intros Y₁ Y₂ f,
  ext1 t,
  ext1 j,
  apply adj.hom_equiv_naturality_right
end

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
def cones_iso {J : Type v} [small_category J] {K : J ⥤ D} :
  F.op ⋙ ((cones J D).obj K) ≅ (cones J C).obj (K ⋙ G) :=
nat_iso.of_components (λ X,
{ hom := λ t,
  { app := λ j, (adj.hom_equiv X (K.obj j)) (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_right, ← t.naturality, category.id_comp, category.id_comp],
      refl
    end },
  inv := λ t,
  { app := λ j, (adj.hom_equiv X (K.obj j)).symm (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_right_symm, ← t.naturality, category.id_comp, category.id_comp]
    end } } )
(by tidy)

end category_theory.adjunction

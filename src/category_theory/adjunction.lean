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

structure adjunction.core_hom_equiv (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π (X Y), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(hom_equiv_naturality_left' : Π {X' X Y} (f : X' ⟶ X) (g : F.obj X ⟶ Y),
  (hom_equiv X' Y) (F.map f ≫ g) = f ≫ (hom_equiv X Y) g . obviously)
(hom_equiv_naturality_right' : Π {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
  (hom_equiv X Y') (f ≫ g) = (hom_equiv X Y) f ≫ G.map g . obviously)

namespace adjunction.core_hom_equiv

restate_axiom hom_equiv_naturality_left'
attribute [simp] hom_equiv_naturality_left
restate_axiom hom_equiv_naturality_right'

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction.core_hom_equiv F G) {X' X : C} {Y Y' : D}

lemma hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶  G.obj Y) :
  (adj.hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.hom_equiv X Y).symm g :=
begin
  rw [← equiv.apply_eq_iff_eq (adj.hom_equiv X' Y)],
  simp
end

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶  G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g :=
begin
  rw [← equiv.apply_eq_iff_eq (adj.hom_equiv X Y')],
  simp [hom_equiv_naturality_right]
end

end adjunction.core_hom_equiv

structure adjunction.core_unit_counit (F : C ⥤ D) (G : D ⥤ C) :=
(unit : functor.id C ⟹ F.comp G)
(counit : G.comp F ⟹ functor.id D)
(left_triangle' : (whisker_right unit F).vcomp (whisker_left F counit) = nat_trans.id _ . obviously)
(right_triangle' : (whisker_left G unit).vcomp (whisker_right counit G) = nat_trans.id _ . obviously)

namespace adjunction.core_unit_counit

restate_axiom left_triangle'
attribute [simp] left_triangle
restate_axiom right_triangle'
attribute [simp] right_triangle

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction.core_unit_counit F G)

lemma left_triangle_components {c : C} :
  F.map (adj.unit.app c) ≫ adj.counit.app (F.obj c) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ functor.id C ⋙ F), nat_trans.app t c) adj.left_triangle

lemma right_triangle_components {d : D} :
  adj.unit.app (G.obj d) ≫ G.map (adj.counit.app d) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ G ⋙ functor.id C), nat_trans.app t d) adj.right_triangle

end adjunction.core_unit_counit

/--
`adjunction F G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) extends
  (adjunction.core_hom_equiv F G), (adjunction.core_unit_counit F G) :=
(unit_hom_equiv : Π {X}, unit.app X = (hom_equiv _ _).to_fun (𝟙 (F.obj X)) . obviously)
(counit_hom_equiv : Π {Y}, counit.app Y = (hom_equiv _ _).inv_fun (𝟙 (G.obj Y)) . obviously)

namespace adjunction
variables (F : C ⥤ D) (G : D ⥤ C)

def of_core_hom_equiv (adj : core_hom_equiv F G) : adjunction F G :=
{ unit :=
  { app := λ X, (adj.hom_equiv _ _).to_fun (𝟙 (F.obj X)),
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
    erw ←adj.hom_equiv_naturality_left_symm,
    simpa using equiv.left_inv (@core_hom_equiv.hom_equiv _ _ _ _ _ _ adj _ _) (𝟙 _)
  end,
  right_triangle' :=
  begin
    ext1, dsimp,
    erw [← adj.hom_equiv_naturality_right],
    simpa using equiv.right_inv (@core_hom_equiv.hom_equiv _ _ _ _ _ _ adj _ _) (𝟙 _)
  end,
  .. adj }

def of_core_unit_counit (adj : core_unit_counit F G) : adjunction F G :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, adj.unit.app X ≫ G.map f,
    inv_fun := λ g, F.map g ≫ adj.counit.app Y,
    left_inv := λ f, begin
      change F.map (_ ≫ _) ≫ _ = _,
      rw [F.map_comp, assoc, ←functor.comp_map, adj.counit.naturality, ←assoc],
      convert id_comp _ f,
      apply adj.left_triangle_components
    end,
    right_inv := λ g, begin
      change _ ≫ G.map (_ ≫ _) = _,
      rw [G.map_comp, ←assoc, ←functor.comp_map, ←adj.unit.naturality, assoc],
      convert comp_id _ g,
      apply adj.right_triangle_components
  end },
  hom_equiv_naturality_left' :=
  begin
    intros X' X Y f g,
    dsimp,
    simp only [category_theory.functor.map_comp],
    erw [← category.assoc, ← category.assoc],
    congr' 1,
    simpa using (adj.unit.naturality f).symm
  end,
  .. adj }

section
variables {F} {G} (adj : adjunction F G) {X' X : C} {Y Y' : D}

def hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :=
adj.to_core_hom_equiv.hom_equiv_naturality_left f g

def hom_equiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :=
adj.to_core_hom_equiv.hom_equiv_naturality_right f g

def hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :=
adj.to_core_hom_equiv.hom_equiv_naturality_left_symm f g

def hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :=
adj.to_core_hom_equiv.hom_equiv_naturality_right_symm f g

def left_triangle := adj.to_core_unit_counit.left_triangle

def right_triangle := adj.to_core_unit_counit.right_triangle

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

def left_adjoint_of_equiv : C ⥤ D :=
{ obj := F_obj,
  map := λ X X' f, (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _)),
  map_comp' := λ X X' X'' f f', begin
    rw [equiv.symm_apply_eq, he, equiv.apply_inverse_apply],
    conv { to_rhs, rw [assoc, ←he, id_comp, equiv.apply_inverse_apply] },
    simp
  end }

def adjunction_of_equiv_left : adjunction (left_adjoint_of_equiv e he) G :=
of_core_hom_equiv (left_adjoint_of_equiv e he) G
{ hom_equiv := e,
  hom_equiv_naturality_left' :=
  begin
    intros X' X Y f h,
    erw [he, equiv.apply_inverse_apply, assoc, ←he, id_comp]
  end
}

end construct_left

section construct_right
-- Construction of a right adjoint, analogous to the above.
variables {F} {G_obj : D → C}
variables (e : Π X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))
variables (he : Π X' X Y f h, e X' Y (F.map f ≫ h) = f ≫ e X Y h)
include he

private lemma he' (X' X Y f h) : F.map f ≫ (e X Y).symm h = (e X' Y).symm (f ≫ h) :=
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
of_core_hom_equiv F (right_adjoint_of_equiv e he)
{ hom_equiv := e,
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

def cocone_equiv {J : Type v} [small_category J] {X : J ⥤ C} {Y : D} :
  ((X ⋙ F) ⟶ ((const J).obj Y)) ≃ (X ⟶ ((const J).obj (G.obj Y))) :=
{ to_fun := λ t,
  { app := λ j, (adj.hom_equiv (X.obj j) Y) (t.app j),
    naturality' := λ j j' f, by erw [← adj.hom_equiv_naturality_left, t.naturality]; dsimp; simp },
  inv_fun := λ t,
  { app := λ j, (adj.hom_equiv (X.obj j) Y).symm (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm, t.naturality],
      dsimp [const], simp
    end },
  left_inv := λ t, by ext j; apply (adj.hom_equiv _ _).left_inv,
  right_inv := λ t, by ext j; apply (adj.hom_equiv _ _).right_inv }

def cone_equiv {J : Type v} [small_category J] {X : C} {Y : J ⥤ D} :
  ((const J).obj (F.obj X) ⟶ Y) ≃ ((const J).obj X ⟶ Y ⋙ G) :=
{ to_fun := λ t,
  { app := λ j, (adj.hom_equiv X (Y.obj j)) (t.app j),
    naturality' := λ j j' f, begin
      erw [←adj.hom_equiv_naturality_left, ←adj.hom_equiv_naturality_right, ←t.naturality],
      dsimp, simp
    end },
  inv_fun := λ t,
  { app := λ j, (adj.hom_equiv X (Y.obj j)).symm (t.app j),
    naturality' := λ j j' f,
      by erw [←adj.hom_equiv_naturality_right_symm, ←t.naturality]; dsimp; simp },
  left_inv := λ t, by ext j; apply (adj.hom_equiv _ _).left_inv,
  right_inv := λ t, by ext j; apply (adj.hom_equiv _ _).right_inv }

section preservation

include adj

-- /-- A left adjoint preserves colimits. -/
-- def left_adjoint_preserves_colimits : preserves_colimits F :=
-- λ J 𝒥 K, by resetI; exact
--  ⟨by exactI λ Y c h, limits.is_colimit.of_equiv
--   (λ Z, calc
--      (F.obj c.X ⟶ Z) ≃ (c.X ⟶ G.obj Z)            : adj.hom_equiv
--      ... ≃ (Y ⟹ (functor.const J).obj (G.obj Z))  : h.equiv
--      ... ≃ (Y.comp F ⟹ (functor.const J).obj Z)   : adj.cocone_equiv.symm)
--   (λ Z f j, begin
--      dsimp [is_colimit.equiv, cocone_equiv],
--      rw adj.hom_equiv_symm_naturality,
--      erw adj.hom_equiv.left_inv f
--    end)⟩

-- /-- A right adjoint preserves limits. -/
-- def right_adjoint_preserves_limits : preserves_limits G :=
-- ⟨λ J 𝒥, by exactI λ Y c h, limits.is_limit.of_equiv
--   (λ Z, calc
--      (Z ⟶ G.obj c.X) ≃ (F.obj Z ⟶ c.X)            : adj.hom_equiv.symm
--      ... ≃ ((functor.const J).obj (F.obj Z) ⟹ Y)  : (h.equiv (F.obj Z)).to_equiv
--      ... ≃ ((functor.const J).obj Z ⟹ Y.comp G)   : adj.cone_equiv)
--   (λ Z f j, begin
--      dsimp [is_limit.equiv, cone_equiv],
--      rw adj.hom_equiv_naturality,
--      erw adj.hom_equiv.right_inv f,
--      simp
--    end)⟩

end preservation

end category_theory.adjunction

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

variables {C : Sort u₁} [𝒞 : category.{v₁} C] {D : Sort u₂} [𝒟 : category.{v₂} D]
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
variables {E : Sort u₃} [ℰ : category.{v₃} E] (H : D ⥤ E) (I : E ⥤ D)

def comp (adj₁ : adjunction F G) (adj₂ : adjunction H I) : adjunction (F ⋙ H) (I ⋙ G) :=
{ hom_equiv := λ X Z, equiv.trans (adj₂.hom_equiv _ _) (adj₁.hom_equiv _ _),
  unit := adj₁.unit ≫
  (whisker_left F $ whisker_right adj₂.unit G) ≫ (functor.associator _ _ _).inv,
  counit := (functor.associator _ _ _).hom ≫
    (whisker_left I $ whisker_right adj₁.counit H) ≫ adj₂.counit }

end

structure is_left_adjoint (left : C ⥤ D) :=
(right : D ⥤ C)
(adj : adjunction left right)

structure is_right_adjoint (right : D ⥤ C) :=
(left : C ⥤ D)
(adj : adjunction left right)

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
    rw [equiv.symm_apply_eq, he, equiv.apply_symm_apply],
    conv { to_rhs, rw [assoc, ←he, id_comp, equiv.apply_symm_apply] },
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
    rw [← equiv.eq_symm_apply, ← he' e he, equiv.symm_apply_apply],
    conv { to_rhs, rw [← assoc, he' e he, comp_id, equiv.symm_apply_apply] },
    simp
  end }

def adjunction_of_equiv_right : adjunction F (right_adjoint_of_equiv e he) :=
mk_of_hom_equiv F (right_adjoint_of_equiv e he)
{ hom_equiv := e,
  hom_equiv_naturality_left_symm' := by intros; rw [equiv.symm_apply_eq, he]; simp,
  hom_equiv_naturality_right' :=
  begin
    intros X Y Y' g h,
    erw [←he, equiv.apply_eq_iff_eq, ←assoc, he' e he, comp_id, equiv.symm_apply_apply]
  end }

end construct_right

end adjunction

end category_theory

namespace category_theory.adjunction
open category_theory
open category_theory.functor
open category_theory.limits

universes u₁ u₂ v

variables {C : Sort u₁} [𝒞 : category.{v+1} C] {D : Sort u₂} [𝒟 : category.{v+1} D]
include 𝒞 𝒟

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction F G)
include adj

section preservation_colimits
variables {J : Type v} [small_category J] (K : J ⥤ C)

def functoriality_is_left_adjoint :
  is_left_adjoint (@cocones.functoriality _ _ _ _ K _ _ F) :=
{ right := (cocones.functoriality G) ⋙ (cocones.precompose
    (K.right_unitor.inv ≫ (whisker_left K adj.unit) ≫ (associator _ _ _).inv)),
  adj := mk_of_unit_counit _ _
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
            adj.counit.naturality (c.ι.app j), ← category.assoc,
            adj.left_triangle_components, category.id_comp],
          refl,
        end },
      naturality' := λ _ _ f, by have := adj.counit.naturality (f.hom); tidy } } }

/-- A left adjoint preserves colimits. -/
def left_adjoint_preserves_colimits : preserves_colimits F :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by resetI; exact
    { preserves := λ c hc, is_colimit_iso_unique_cocone_morphism.inv
        (λ s, (((adj.functoriality_is_left_adjoint _).adj).hom_equiv _ _).unique_of_equiv $
          is_colimit_iso_unique_cocone_morphism.hom hc _ ) } } }

end preservation_colimits

section preservation_limits
variables {J : Type v} [small_category J] (K : J ⥤ D)

def functoriality_is_right_adjoint :
  is_right_adjoint (@cones.functoriality _ _ _ _ K _ _ G) :=
{ left := (cones.functoriality F) ⋙ (cones.postcompose
    ((associator _ _ _).hom ≫ (whisker_left K adj.counit) ≫ K.right_unitor.hom)),
  adj := mk_of_unit_counit _ _
  { unit :=
    { app := λ c,
      { hom := adj.unit.app c.X,
        w' :=
        begin
          intro j,
          dsimp,
          erw [category.comp_id, category.id_comp, G.map_comp, ← category.assoc,
            ← adj.unit.naturality (c.π.app j), category.assoc,
            adj.right_triangle_components, category.comp_id],
          refl,
        end },
      naturality' := λ _ _ f, by have := adj.unit.naturality (f.hom); tidy },
    counit :=
    { app := λ c,
      { hom := adj.counit.app c.X,
        w' := λ j, by have := adj.counit.naturality (c.π.app j); tidy },
      naturality' := λ _ _ f, by have := adj.counit.naturality (f.hom); tidy } } }

/-- A right adjoint preserves limits. -/
def right_adjoint_preserves_limits : preserves_limits G :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ K,
    by resetI; exact
    { preserves := λ c hc, is_limit_iso_unique_cone_morphism.inv
        (λ s, (((adj.functoriality_is_right_adjoint _).adj).hom_equiv _ _).symm.unique_of_equiv $
          is_limit_iso_unique_cone_morphism.hom hc _) }

end preservation_limits

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
def cocones_iso {J : Type v} [small_category J] {K : J ⥤ C} :
  (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ ((cocones J C).obj (op K)) :=
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
  { app := λ j, (adj.hom_equiv (unop X) (K.obj j)) (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_right, ← t.naturality, category.id_comp, category.id_comp],
      refl
    end },
  inv := λ t,
  { app := λ j, (adj.hom_equiv (unop X) (K.obj j)).symm (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_right_symm, ← t.naturality, category.id_comp, category.id_comp]
    end } } )
(by tidy)

end category_theory.adjunction

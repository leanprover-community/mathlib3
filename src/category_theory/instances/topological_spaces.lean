-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.concrete_category
import category_theory.full_subcategory
import category_theory.adjunction
import category_theory.limits.types
import category_theory.eq_to_hom
import topology.opens

open category_theory
open category_theory.nat_iso
open topological_space

universe u

namespace category_theory.instances

/-- The category of topological spaces and continuous maps. -/
@[reducible] def Top : Type (u+1) := bundled topological_space

instance (x : Top) : topological_space x := x.str

namespace Top
instance : concrete_category @continuous := ⟨@continuous_id, @continuous.comp⟩

section
open category_theory.limits

variables {J : Type u} [small_category J]

def limit (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨limit (F ⋙ forget), ⨆ j, (F.obj j).str.induced (limit.π (F ⋙ forget) j)⟩,
  π :=
  { app := λ j, ⟨limit.π (F ⋙ forget) j, continuous_iff_induced_le.mpr (lattice.le_supr _ j)⟩,
    naturality' := λ j j' f, subtype.eq ((limit.cone (F ⋙ forget)).π.naturality f) } }

def limit_is_limit (F : J ⥤ Top.{u}) : is_limit (limit F) :=
by refine is_limit.of_faithful forget (limit.is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl);
   exact continuous_iff_le_coinduced.mpr (lattice.supr_le $ λ j,
     induced_le_iff_le_coinduced.mpr $ continuous_iff_le_coinduced.mp (s.π.app j).property)

instance : has_limits.{u} Top.{u} :=
λ J 𝒥 F, by exactI { cone := limit F, is_limit := limit_is_limit F }

instance : preserves_limits (forget : Top.{u} ⥤ Type u) :=
λ J 𝒥 F, by exactI preserves_limit_of_preserves_limit_cone
  (limit.is_limit F) (limit.is_limit (F ⋙ forget))

def colimit (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨colimit (F ⋙ forget), ⨅ j, (F.obj j).str.coinduced (colimit.ι (F ⋙ forget) j)⟩,
  ι :=
  { app := λ j, ⟨colimit.ι (F ⋙ forget) j, continuous_iff_le_coinduced.mpr (lattice.infi_le _ j)⟩,
    naturality' := λ j j' f, subtype.eq ((colimit.cocone (F ⋙ forget)).ι.naturality f) } }

def colimit_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit F) :=
by refine is_colimit.of_faithful forget (colimit.is_colimit _) (λ s, ⟨_, _⟩) (λ s, rfl);
   exact continuous_iff_induced_le.mpr (lattice.le_infi $ λ j,
     induced_le_iff_le_coinduced.mpr $ continuous_iff_le_coinduced.mp (s.ι.app j).property)

instance : has_colimits.{u} Top.{u} :=
λ J 𝒥 F, by exactI { cocone := colimit F, is_colimit := colimit_is_colimit F }

instance : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
λ J 𝒥 F, by exactI preserves_colimit_of_preserves_colimit_cocone
  (colimit.is_colimit F) (colimit.is_colimit (F ⋙ forget))

end

def discrete : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊤⟩,
  map := λ X Y f, ⟨f, continuous_top⟩ }

def trivial : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊥⟩,
  map := λ X Y f, ⟨f, continuous_bot⟩ }

def adj₁ : adjunction discrete forget :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, f,
    inv_fun := λ f, ⟨f, continuous_top⟩,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, id },
  counit := { app := λ X, ⟨id, continuous_top⟩ } }

def adj₂ : adjunction forget trivial :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f, continuous_bot⟩,
    inv_fun := λ f, f,
    left_inv := by tidy,
    right_inv := by tidy },
  unit := { app := λ X, ⟨id, continuous_bot⟩ },
  counit := { app := λ X, id } }

end Top

variables {X : Top.{u}}

instance : category.{u+1} (opens X) :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans f.down.down g.down.down ⟩ ⟩ }

def open_nhds (x : X.α) := { U : opens X // x ∈ U }
instance open_nhds_category (x : X.α) : category (open_nhds x) := begin unfold open_nhds, apply_instance end

end category_theory.instances

open category_theory.instances

namespace topological_space.opens

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map
  {X Y : Top.{u}} (f : X ⟶ Y) : opens Y ⥤ opens X :=
{ obj := λ U, ⟨ f.val ⁻¹' U, f.property _ U.property ⟩,
  map := λ U V i, ⟨ ⟨ λ a b, i.down.down b ⟩ ⟩ }.

@[simp] lemma map_id_obj' {X : Top.{u}} (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
rfl

@[simp] lemma map_id_obj {X : Top.{u}} (U : opens X) : (map (𝟙 X)).obj U = U :=
by { ext, refl } -- not quite `rfl`, since we don't have eta for records

@[simp] lemma map_id_obj_unop {X : Top.{u}} (U : (opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
by simp
@[simp] lemma op_map_id_obj {X : Top.{u}} (U : (opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U :=
by simp

def map_id (X : Top.{u}) : map (𝟙 X) ≅ functor.id (opens X) :=
{ hom := { app := λ U, eq_to_hom (map_id_obj U) },
  inv := { app := λ U, eq_to_hom (map_id_obj U).symm } }

@[simp] lemma map_id_hom_app (X : Top.{u}) (U) : (map_id X).hom.app U = eq_to_hom (map_id_obj U) := rfl
@[simp] lemma map_id_inv_app (X : Top.{u}) (U) : (map_id X).inv.app U = eq_to_hom (map_id_obj U).symm := rfl

@[simp] lemma map_comp_obj' {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) : (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
rfl

@[simp] lemma map_comp_obj {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
by { ext, refl } -- not quite `rfl`, since we don't have eta for records

@[simp] lemma map_comp_obj_unop {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
by simp
@[simp] lemma op_map_comp_obj {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
by simp

def map_comp {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
{ hom := { app := λ U, eq_to_hom (map_comp_obj f g U) },
  inv := { app := λ U, eq_to_hom (map_comp_obj f g U).symm } }

@[simp] lemma map_comp_hom_app {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map_comp f g).hom.app U = eq_to_hom (map_comp_obj f g U) := rfl
@[simp] lemma map_comp_inv_app {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map_comp f g).inv.app U = eq_to_hom (map_comp_obj f g U).symm := rfl

-- We could make f g implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def map_iso {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg functor.obj (congr_arg map h)) U) ) (by obviously)

@[simp] lemma map_iso_refl {X Y : Top.{u}} (f : X ⟶ Y) (h) : map_iso f f h = iso.refl (map _) := rfl

@[simp] lemma map_iso_hom_app {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).hom.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h)) U) :=
rfl

@[simp] lemma map_iso_inv_app {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).inv.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h.symm)) U) :=
rfl

end topological_space.opens

open topological_space

namespace topological_space.open_nhds
variables {X Y : Top.{u}} (f : X ⟶ Y)

def inclusion (x : X.α) : open_nhds x ⥤ opens X :=
{ obj := λ U, U.val,
  map := λ U V i, i }

@[simp] lemma inclusion_obj (x : X.α) (U) (p) : (inclusion x).obj ⟨U,p⟩ = U := rfl

def map (x : X) : open_nhds (f x) ⥤ open_nhds x :=
{ obj := λ U, ⟨(opens.map f).obj U.1, by tidy⟩,
  map := λ U V i, (opens.map f).map i }

@[simp] lemma map_id_obj' {X : Top.{u}} (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
rfl
@[simp] lemma map_id_obj {X : Top.{u}} (x : X) (U) : (map (𝟙 X) x).obj U = U :=
by tidy

@[simp] lemma map_id_obj_unop {X : Top.{u}} (x : X) (U : (open_nhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U :=
by simp
@[simp] lemma op_map_id_obj {X : Top.{u}} (x : X) (U : (open_nhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U :=
by simp

def inclusion_map_iso (x : X) : inclusion (f x) ⋙ opens.map f ≅ map f x ⋙ inclusion x :=
nat_iso.of_components
  (λ U, begin split, exact 𝟙 _, exact 𝟙 _ end)
  (by tidy)

@[simp] lemma inclusion_map_iso_hom (x : X) : (inclusion_map_iso f x).hom = 𝟙 _ := rfl
@[simp] lemma inclusion_map_iso_inv (x : X) : (inclusion_map_iso f x).inv = 𝟙 _ := rfl

end topological_space.open_nhds

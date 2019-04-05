-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.concrete_category
import category_theory.full_subcategory
import category_theory.functor_category
import category_theory.adjunction
import category_theory.limits.types
import category_theory.natural_isomorphism
import category_theory.eq_to_hom
import topology.basic
import topology.opens
import order.galois_connection

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

-- local attribute [class] continuous
-- instance {R S : Top} (f : R ⟶ S) : continuous (f : R → S) := f.2

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

-- To avoid mucky about with opposite categories, we just define the morphisms
-- in the direction we're always going to want to use.
instance : category.{u+1} (opens X) :=
{ hom  := λ U V, ulift (plift (U ≥ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ ge_trans f.down.down g.down.down ⟩ ⟩ }
-- instance : category.{0} (opens X) :=
-- { hom  := λ U V, U ≥ V,
--   id   := λ X, le_refl X,
--   comp := λ X Y Z f g, ge_trans f g }

def nbhds (x : X.α) := { U : opens X // x ∈ U }
instance nbhds_category (x : X.α) : category (nbhds x) := begin unfold nbhds, apply_instance end

def nbhds_inclusion (x : X.α) : nbhds x ⥤ opens X :=
{ obj := λ U, U.val,
  map := λ U V i, i }

end category_theory.instances

open category_theory.instances

namespace topological_space.opens

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map
  {X Y : Top.{u}} (f : X ⟶ Y) : opens Y ⥤ opens X :=
{ obj := λ U, ⟨ f.val ⁻¹' U, f.property _ U.property ⟩,
  map := λ U V i, ⟨ ⟨ λ a b, i.down.down b ⟩ ⟩ }.

@[simp] lemma map_id_obj {X : Top.{u}} (U : opens X) : (map (𝟙 X)).obj U = U := by tidy

@[simp] def map_id (X : Top.{u}) : map (𝟙 X) ≅ functor.id (opens X) :=
{ hom := { app := λ U, 𝟙 U },
  inv := { app := λ U, 𝟙 U } }

@[simp] def map_comp {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
{ hom := { app := λ U, 𝟙 _ },
  inv := { app := λ U, 𝟙 _ } }

-- We could make f g implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def map_iso {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg _ (congr_arg _ h)) _) ) (by obviously)

-- @[simp] lemma map_iso_id {X : Top.{u}} (h) : map_iso (𝟙 X) (𝟙 X) h = iso.refl (map _) := rfl
@[simp] lemma map_iso_refl {X Y : Top.{u}} (f : X ⟶ Y) (h) : map_iso f f h = iso.refl (map _) := rfl

@[simp] lemma map_iso_hom_app {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).hom.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h)) U) :=
rfl

@[simp] lemma map_iso_inv_app {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).inv.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h.symm)) U) :=
rfl

end topological_space.opens

open topological_space

namespace topological_space.nbhds
variables {X Y : Top.{u}} (f : X ⟶ Y)

def map (x : X) : nbhds (f x) ⥤ nbhds x :=
{ obj := λ U, ⟨(opens.map f).obj U.1, by tidy⟩,
  map := λ U V i, (opens.map f).map i }

@[simp] lemma map_id_obj (x : X) (U : nbhds x) : (map (𝟙 X) x).obj U = U := by tidy

def inclusion_map_iso (x : X) : nbhds_inclusion (f x) ⋙ opens.map f ≅ map f x ⋙ nbhds_inclusion x :=
nat_iso.of_components
  (λ U, begin split, exact 𝟙 _, exact 𝟙 _ end)
  (by tidy)

@[simp] lemma inclusion_map_iso_hom (x : X) : (inclusion_map_iso f x).hom = 𝟙 _ := rfl
@[simp] lemma inclusion_map_iso_inv (x : X) : (inclusion_map_iso f x).inv = 𝟙 _ := rfl

end topological_space.nbhds

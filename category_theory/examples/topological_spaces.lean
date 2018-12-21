-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.full_subcategory
import category_theory.functor_category
import category_theory.limits.preserves
import category_theory.limits.types
import category_theory.natural_isomorphism
import category_theory.eq_to_hom
import analysis.topology.topological_space
import analysis.topology.continuity
import order.galois_connection

open category_theory
open category_theory.nat_iso
open topological_space

universe u

namespace category_theory.examples

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

instance : has_limits.{u+1 u} Top.{u} :=
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

instance : has_colimits.{u+1 u} Top.{u} :=
λ J 𝒥 F, by exactI { cocone := colimit F, is_colimit := colimit_is_colimit F }

instance : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
λ J 𝒥 F, by exactI preserves_colimit_of_preserves_colimit_cocone
  (colimit.is_colimit F) (colimit.is_colimit (F ⋙ forget))

end
end Top

variables {X : Top.{u}}

instance : small_category (opens X) := by apply_instance

def nbhd (x : X.α) := { U : opens X // x ∈ U }
def nbhds (x : X.α) : small_category (nbhd x) := begin unfold nbhd, apply_instance end

end category_theory.examples

open category_theory.examples

namespace topological_space.opens

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map
  {X Y : Top.{u}} (f : X ⟶ Y) : opens Y ⥤ opens X :=
{ obj := λ U, ⟨ f.val ⁻¹' U, f.property _ U.property ⟩,
  map := λ U V i, ⟨ ⟨ λ a b, i.down.down b ⟩ ⟩ }.

@[simp] lemma map_id_obj (X : Top.{u}) (U : opens X) : (map (𝟙 X)).obj U = U := by tidy

@[simp] def map_id (X : Top.{u}) : map (𝟙 X) ≅ functor.id (opens X) :=
{ hom := { app := λ U, 𝟙 U },
  inv := { app := λ U, 𝟙 U } }

-- We could make f g implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def map_iso {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg _ (congr_arg _ h)) _) ) (by obviously)

@[simp] def map_iso_id {X : Top.{u}} (h) : map_iso (𝟙 X) (𝟙 X) h = iso.refl (map _) := rfl

end topological_space.opens
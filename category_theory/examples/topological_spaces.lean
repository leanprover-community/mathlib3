-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.full_subcategory
import category_theory.functor_category
import category_theory.natural_isomorphism
import analysis.topology.topological_space
import analysis.topology.continuity

open category_theory
universe u

namespace category_theory.examples

/-- The category of topological spaces and continuous maps. -/
@[reducible] def Top : Type (u+1) := bundled topological_space

instance (x : Top) : topological_space x := x.str

namespace Top
instance : concrete_category @continuous := ⟨@continuous_id, @continuous.comp⟩

-- local attribute [class] continuous
-- instance {R S : Top} (f : R ⟶ S) : continuous (f : R → S) := f.2
end Top

structure open_set (X : Top.{u}) : Type u :=
(s : set X.α)
(is_open : topological_space.is_open X.str s)

variables {X : Top.{u}}

namespace open_set
instance : has_coe (open_set X) (set X.α) := { coe := λ U, U.s }

instance : has_subset (open_set X) :=
{ subset := λ U V, U.s ⊆ V.s }

instance : preorder (open_set X) := by refine { le := (⊇), .. } ; tidy

instance open_sets : small_category (open_set X) := by apply_instance

instance : has_mem X.α (open_set X) :=
{ mem := λ a V, a ∈ V.s }

def nbhd (x : X.α) := { U : open_set X // x ∈ U }
def nbhds (x : X.α) : small_category (nbhd x) := begin unfold nbhd, apply_instance end

/-- `open_set.map f` gives the functor from open sets in Y to open set in X, 
    given by taking preimages under f. -/
def map
  {X Y : Top} (f : X ⟶ Y) : open_set Y ⥤ open_set X :=
{ obj := λ U, ⟨ f.val ⁻¹' U.s, f.property _ U.is_open ⟩,
  map' := λ U V i, ⟨ ⟨ λ a b, i.down.down b ⟩ ⟩ }.

@[simp] def map_id (X : Top) : map (𝟙 X) ≅ functor.id (open_set X) := 
{ hom := { app := λ U, 𝟙 U },
  inv := { app := λ U, 𝟙 U } }

def map_iso {X Y : Top} {f g : X ⟶ Y} (h : f = g) : map f ≅ map g := 
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg _ (congr_arg _ h)) _) ) (by obviously)

end open_set

end category_theory.examples

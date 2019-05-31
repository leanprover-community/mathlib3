-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import topology.Top.opens
import category_theory.full_subcategory

open category_theory
open topological_space
open opposite

universe u

namespace topological_space.open_nhds
variables {X Y : Top.{u}} (f : X ⟶ Y)

def open_nhds (x : X.α) := { U : opens X // x ∈ U }
instance open_nhds_category (x : X.α) : category.{u+1} (open_nhds x) := by {unfold open_nhds, apply_instance}

def inclusion (x : X.α) : open_nhds x ⥤ opens X :=
full_subcategory_inclusion _

@[simp] lemma inclusion_obj (x : X.α) (U) (p) : (inclusion x).obj ⟨U,p⟩ = U := rfl

def map (x : X) : open_nhds (f x) ⥤ open_nhds x :=
{ obj := λ U, ⟨(opens.map f).obj U.1, by tidy⟩,
  map := λ U V i, (opens.map f).map i }

@[simp] lemma map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(opens.map f).obj U, by tidy⟩ :=
rfl
@[simp] lemma map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
rfl
@[simp] lemma map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U :=
by tidy

@[simp] lemma map_id_obj_unop (x : X) (U : (open_nhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U :=
by simp
@[simp] lemma op_map_id_obj (x : X) (U : (open_nhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U :=
by simp

def inclusion_map_iso (x : X) : inclusion (f x) ⋙ opens.map f ≅ map f x ⋙ inclusion x :=
nat_iso.of_components
  (λ U, begin split, exact 𝟙 _, exact 𝟙 _ end)
  (by tidy)

@[simp] lemma inclusion_map_iso_hom (x : X) : (inclusion_map_iso f x).hom = 𝟙 _ := rfl
@[simp] lemma inclusion_map_iso_inv (x : X) : (inclusion_map_iso f x).inv = 𝟙 _ := rfl

end topological_space.open_nhds

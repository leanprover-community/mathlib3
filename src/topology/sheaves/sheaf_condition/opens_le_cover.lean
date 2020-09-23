/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.limits.limits
import category_theory.full_subcategory
import topology.sheaves.sheaf_condition.pairwise_intersections

/-!
Another version of the sheaf condition, from Lurie SAG.
-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_limits C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

namespace sheaf_condition

/--
The category of open sets contained in some element of the cover.
-/
@[derive category]
def opens_le_cover : Type v := { V : opens X // ∃ i, V ≤ U i }

namespace opens_le_cover

variables {U}

def index (V : opens_le_cover U) : ι := V.property.some

def hom_to_index (V : opens_le_cover U) : V.val ⟶ U (index V) :=
hom_of_le (V.property.some_spec)

end opens_le_cover

/--
`supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opens_le_cover_cone : cocone (full_subcategory_inclusion _ : opens_le_cover U ⥤ opens X) :=
{ X := supr U,
  ι := { app := λ V, V.hom_to_index ≫ opens.le_supr U i, } }

end sheaf_condition

open sheaf_condition

@[derive subsingleton]
def sheaf_condition_opens_le_cover : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (opens_le_cover_cone U).op)

-- It seems that proving this is equivalent to the usual sheaf condition should use cofinality.

namespace sheaf_condition

def pairwise_to_opens_le_cover_obj : pairwise U → opens_le_cover U
| single i := ⟨U i, ⟨i, le_refl _⟩⟩
| pair i j := ⟨U i ⊓ U j, ⟨i, inf_le_left _ _⟩⟩

def pairwise_to_opens_le_cover_map :
  Π {V W : pairwise U}, (V ⟶ W) → (pairwise_to_opens_le_cover_obj V ⟶ pairwise_to_opens_le_cover_obj W)
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _

def pairwise_to_opens_le_cover : pairwise U ⥤ opens_le_cover U :=
{ obj := pairwise_to_opens_le_cover_obj,
  hom := λ V W i, pairwise_to_opens_le_cover_map i, }

instance : cofinal (pairwise_to_opens_le_cover U) := sorry

end sheaf_condition

end presheaf

end Top

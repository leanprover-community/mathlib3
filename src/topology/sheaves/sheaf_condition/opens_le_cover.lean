/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.full_subcategory
import category_theory.limits.cofinal
import topology.sheaves.sheaf_condition.pairwise_intersections

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → opens X` we can form the subcategory
`{ V : opens X // ∃ i, V ≤ U i }`, which has `supr U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

## References
* This is the definition Lurie uses in "Spectral Algebraic Geometry".
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
def opens_le_cover : Type v := { V : opens X // ∃ i, V ≤ U i }

instance : category (opens_le_cover U) := category_theory.full_subcategory _

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
  ι := { app := λ V : opens_le_cover U, V.hom_to_index ≫ opens.le_supr U _, } }

end sheaf_condition

open sheaf_condition

@[derive subsingleton]
def sheaf_condition_opens_le_cover : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (opens_le_cover_cone U).op)

-- It seems that proving this is equivalent to the usual sheaf condition should use cofinality.

namespace sheaf_condition

open category_theory.pairwise

@[simp]
def pairwise_to_opens_le_cover_obj : pairwise ι → opens_le_cover U
| (single i) := ⟨U i, ⟨i, le_refl _⟩⟩
| (pair i j) := ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩

-- @[simp] lemma pairwise_to_opens_le_cover_obj_single (i) :
--   pairwise_to_opens_le_cover_obj U (single i) = op ⟨U i, ⟨i, le_refl _⟩⟩ := rfl

open category_theory.pairwise.hom

def pairwise_to_opens_le_cover_map :
  Π {V W : pairwise ι}, (V ⟶ W) → (pairwise_to_opens_le_cover_obj U V ⟶ pairwise_to_opens_le_cover_obj U W)
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := begin apply has_hom.hom.op, exact (hom_of_le inf_le_left), end
| _ _ (right i j) := begin apply has_hom.hom.op, exact (hom_of_le inf_le_right), end

@[simps]
def pairwise_to_opens_le_cover : (pairwise ι)ᵒᵖ ⥤ (opens_le_cover U)ᵒᵖ :=
{ obj := λ V, pairwise_to_opens_le_cover_obj U (unop V),
  map := λ V W i, pairwise_to_opens_le_cover_map U i, }

instance (V : opens_le_cover U) :
  nonempty (comma (functor.from_punit V) (pairwise_to_opens_le_cover U).left_op) :=
⟨{ right := op (single (V.index)), hom := V.hom_to_index }⟩

instance : cofinal (pairwise_to_opens_le_cover U).left_op :=
λ V, is_connected_of_zigzag (λ A B,
  begin
    rcases A with ⟨⟨⟩, ⟨i⟩|⟨i,j⟩, a⟩;
    rcases B with ⟨⟨⟩, ⟨i'⟩|⟨i',j'⟩, b⟩;
    dsimp at *,
    { refine ⟨[{ right := pair i i', hom := hom_of_le (le_inf (le_of_hom a) (le_of_hom b)), }, _], _, _⟩,
      swap 3, refl,
      constructor, right, fsplit, exact { right := begin dsimp, exact left i i', end }, },
    sorry, sorry, sorry,
  end
  )

end sheaf_condition

end presheaf

end Top

/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
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

/--
An arbitrarily chosen index such that `V ≤ U i`.
-/
def index (V : opens_le_cover U) : ι := V.property.some

/--
The morphism from `V` to `U i` for some `i`.
-/
def hom_to_index (V : opens_le_cover U) : V.val ⟶ U (index V) :=
hom_of_le (V.property.some_spec)

end opens_le_cover

/--
`supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opens_le_cover_cocone : cocone (full_subcategory_inclusion _ : opens_le_cover U ⥤ opens X) :=
{ X := supr U,
  ι := { app := λ V : opens_le_cover U, V.hom_to_index ≫ opens.le_supr U _, } }

end sheaf_condition

open sheaf_condition

/--
An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`sheaf_condition_equiv_sheaf_condition_opens_le_cover`).

A presheaf is a sheaf if `F` sends the cone `(opens_le_cover_cocone U).op` to a limit cone.
(Recall `opens_le_cover_cocone U`, has cone point `supr U`,
mapping down to any `V` which is contained in some `U i`.)
-/
@[derive subsingleton]
def sheaf_condition_opens_le_cover : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (opens_le_cover_cocone U).op)

namespace sheaf_condition

open category_theory.pairwise

@[simp]
def pairwise_to_opens_le_cover_obj : pairwise ι → opens_le_cover U
| (single i) := ⟨U i, ⟨i, le_refl _⟩⟩
| (pair i j) := ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩

open category_theory.pairwise.hom

def pairwise_to_opens_le_cover_map :
  Π {V W : pairwise ι}, (V ⟶ W) → (pairwise_to_opens_le_cover_obj U V ⟶ pairwise_to_opens_le_cover_obj U W)
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := hom_of_le inf_le_left
| _ _ (right i j) := hom_of_le inf_le_right

@[simps]
def pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U :=
{ obj := pairwise_to_opens_le_cover_obj U,
  map := λ V W i, pairwise_to_opens_le_cover_map U i, }

def bar : pairwise_to_opens_le_cover U ⋙ full_subcategory_inclusion _ ≅ pairwise.diagram U :=
{ hom := { app := begin rintro (i|⟨i,j⟩); exact 𝟙 _, end, },
  inv := { app := begin rintro (i|⟨i,j⟩); exact 𝟙 _, end, }, }

def foo : (opens_le_cover_cocone U).whisker (pairwise_to_opens_le_cover U) ≅ pairwise.cocone U :=
sorry

instance (V : opens_le_cover U) :
  nonempty (comma (functor.from_punit V) (pairwise_to_opens_le_cover U)) :=
⟨{ right := single (V.index), hom := V.hom_to_index }⟩

instance : cofinal (pairwise_to_opens_le_cover U) :=
λ V, is_connected_of_zigzag (λ A B,
  begin
    rcases A with ⟨⟨⟩, ⟨i⟩|⟨i,j⟩, a⟩;
    rcases B with ⟨⟨⟩, ⟨i'⟩|⟨i',j'⟩, b⟩;
    dsimp at *,
    { refine ⟨[
      { left := punit.star, right := pair i i',
        hom := hom_of_le (le_inf (le_of_hom a) (le_of_hom b)), }, _], _, rfl⟩,
      exact
        list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
          (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩) list.chain.nil) },
    { refine ⟨[
      { left := punit.star, right := pair i' i,
        hom := hom_of_le (le_inf ((le_of_hom b).trans inf_le_left) (le_of_hom a)), },
      { left := punit.star, right := single i',
        hom := hom_of_le ((le_of_hom b).trans inf_le_left), }, _], _, rfl⟩,
      exact
        list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := right i' i, }⟩)
          (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i' i, }⟩)
            (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i' j', }⟩) list.chain.nil)) },
    { refine ⟨[
      { left := punit.star, right := single i,
        hom := hom_of_le ((le_of_hom a).trans inf_le_left), },
      { left := punit.star, right := pair i i', hom :=
        hom_of_le (le_inf ((le_of_hom a).trans inf_le_left) (le_of_hom b)), }, _], _, rfl⟩,
      exact
        list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i j, }⟩)
          (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
            (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩) list.chain.nil)) },
    { refine ⟨[
      { left := punit.star, right := single i,
        hom := hom_of_le ((le_of_hom a).trans inf_le_left), },
      { left := punit.star, right := pair i i',
        hom := hom_of_le (le_inf ((le_of_hom a).trans inf_le_left) ((le_of_hom b).trans inf_le_left)), },
      { left := punit.star, right := single i',
        hom := hom_of_le ((le_of_hom b).trans inf_le_left), }, _], _, rfl⟩,
      exact
        list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i j, }⟩)
          (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
            (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩)
              (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i' j', }⟩) list.chain.nil))), },
  end)

end sheaf_condition

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections (F : presheaf C X) :
  F.sheaf_condition_opens_le_cover ≃ F.sheaf_condition_pairwise_intersections :=
equiv.Pi_congr_right (λ i, equiv.Pi_congr_right (λ U,
  equiv_of_subsingleton_of_subsingleton
    (λ P, begin  end)
    begin sorry, end))

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_equiv_sheaf_condition_opens_le_cover (F : presheaf C X) :
  F.sheaf_condition ≃ F.sheaf_condition_opens_le_cover :=
equiv.trans
  (sheaf_condition_equiv_sheaf_condition_pairwise_intersections F)
  (sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections F).symm

end presheaf

end Top

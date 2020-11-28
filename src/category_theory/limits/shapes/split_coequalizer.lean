/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.kernel_pair

namespace category_theory

universes v v₂ u u₂

variables {C : Type u} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)
variables {X Y : C} (f g : X ⟶ Y)

/--
A split coequalizer diagram consists of morphisms

      f   h
    X ⇉ Y → Z
      g

satisfying `f ≫ h = g ≫ h` together with morphisms

      t   s
    X ← Y ← Z

satisfying `s ≫ h = 𝟙 Z`, `t ≫ g = 𝟙 Y` and `t ≫ f = h ≫ s`.

The name "coequalizer" is appropriate, since any split coequalizer is a coequalizer, see
`is_split_coequalizer.is_coequalizer`.
Split coequalizers are also absolute, since a functor preserves all the structure above.
-/
def is_split_coequalizer {Z : C} (h : Y ⟶ Z) : Prop :=
f ≫ h = g ≫ h ∧ ∃ (s : Z ⟶ Y) (t : Y ⟶ X), s ≫ h = 𝟙 Z ∧ t ≫ g = 𝟙 Y ∧ t ≫ f = h ≫ s

variables {f g}
@[simp, reassoc]
lemma is_split_coequalizer.condition {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) :
  f ≫ h = g ≫ h := q.1

noncomputable def is_split_coequalizer.right_splitting
  {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) : Z ⟶ Y :=
q.2.some

noncomputable def is_split_coequalizer.left_splitting
  {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) : Y ⟶ X :=
q.2.some_spec.some

@[reassoc, simp]
lemma is_split_coequalizer.right_splitting_π
  {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) :
  q.right_splitting ≫ h = 𝟙 _ :=
q.2.some_spec.some_spec.1

@[reassoc, simp]
lemma is_split_coequalizer.left_splitting_bottom
  {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) :
  q.left_splitting ≫ g = 𝟙 _ :=
q.2.some_spec.some_spec.2.1

@[reassoc, simp]
lemma is_split_coequalizer.left_splitting_top
  {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) :
  q.left_splitting ≫ f = h ≫ q.right_splitting :=
q.2.some_spec.some_spec.2.2

/-- Split coequalizers are absolute: they are preserved by any functor. -/
lemma is_split_coequalizer.map {Z : C} {h : Y ⟶ Z} (q : is_split_coequalizer f g h) (F : C ⥤ D) :
  is_split_coequalizer (F.map f) (F.map g) (F.map h) :=
begin
  refine ⟨_, F.map q.right_splitting, F.map q.left_splitting, _, _, _⟩,
  { rw [←F.map_comp, q.condition, F.map_comp] },
  { rw [←F.map_comp, q.right_splitting_π, F.map_id] },
  { rw [←F.map_comp, q.left_splitting_bottom, F.map_id] },
  { rw [←F.map_comp, q.left_splitting_top, F.map_comp] }
end

section

open limits

/-- A split coequalizer clearly induces a cofork. -/
def is_split_coequalizer.as_cofork {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) :
  cofork f g :=
cofork.of_π h t.condition

@[simp] lemma split_coequalizer.as_cofork_π {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) :
  t.as_cofork.π = h := rfl

/--
The cofork induced by a split coequalizer is a coequalizer, justifying the name. In some cases it
is more convenient to show a given cofork is a coequalizer by showing it is split.
-/
noncomputable def is_split_coequalizer.is_coequalizer
  {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) :
  is_colimit t.as_cofork :=
cofork.is_colimit.mk' _ $ λ s,
⟨t.right_splitting ≫ s.π,
 by { dsimp, rw [← t.left_splitting_top_assoc, s.condition, t.left_splitting_bottom_assoc] },
 λ m hm, by { dsimp at hm, rw [← hm, t.right_splitting_π_assoc] }⟩

end

variables (f g)
/--
The pair `f,g` is a split pair if there is a `h : Y ⟶ Z` so that `f, g, h` forms a split coequalizer
in `C`.
-/
class is_split_pair : Prop :=
(splittable [] : ∃ {Z : C} (h : Y ⟶ Z), is_split_coequalizer f g h)

/--
The pair `f,g` is a `G`-split pair if there is a `h : G Y ⟶ Z` so that `G f, G g, h` forms a split
coequalizer in `D`.
-/
abbreviation functor.is_split_pair : Prop := is_split_pair (G.map f) (G.map g)

/-- Get the coequalizer object from the typeclass `is_split_pair`. -/
noncomputable def is_split_pair.coequalizer_of_split [is_split_pair f g] : C :=
(is_split_pair.splittable f g).some

/-- Get the coequalizer morphism from the typeclass `is_split_pair`. -/
noncomputable def is_split_pair.coequalizer_ι [is_split_pair f g] :
  Y ⟶ is_split_pair.coequalizer_of_split f g :=
(is_split_pair.splittable f g).some_spec.some

/-- The coequalizer morphism `coequalizer_ι` gives a split coequalizer on `f,g`. -/
lemma is_split_pair.is_split_coequalizer [is_split_pair f g] :
  is_split_coequalizer f g (is_split_pair.coequalizer_ι f g) :=
(is_split_pair.splittable f g).some_spec.some_spec

/-- If `f, g` is split, then `G f, G g` is split. -/
instance map_is_split_pair [is_split_pair f g] : is_split_pair (G.map f) (G.map g) :=
{ splittable := ⟨_, _, is_split_coequalizer.map (is_split_pair.is_split_coequalizer f g) _⟩ }

namespace limits

/-- If a pair is split, it has a coequalizer. -/
@[priority 1]
instance has_coequalizer_of_is_split_pair [is_split_pair f g] : has_coequalizer f g :=
has_colimit.mk ⟨_, (is_split_pair.is_split_coequalizer f g).is_coequalizer⟩

end limits

end category_theory

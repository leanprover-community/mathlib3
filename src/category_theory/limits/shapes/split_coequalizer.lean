/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.equalizers

/-!
# Split coequalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split
coequalizer: there is a section `s` of `π` and a section `t` of `g`, which additionally satisfy
`t ≫ f = π ≫ s`.

In addition, we show that every split coequalizer is a coequalizer
(`category_theory.is_split_coequalizer.is_coequalizer`) and absolute
(`category_theory.is_split_coequalizer.map`)

A pair `f g : X ⟶ Y` has a split coequalizer if there is a `Z` and `π : Y ⟶ Z` making `f,g,π` a
split coequalizer.
A pair `f g : X ⟶ Y` has a `G`-split coequalizer if `G f, G g` has a split coequalizer.

These definitions and constructions are useful in particular for the monadicity theorems.

## TODO

Dualise to split equalizers.
-/

namespace category_theory

universes v v₂ u u₂

variables {C : Type u} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)
variables {X Y : C} (f g : X ⟶ Y)

/--
A split coequalizer diagram consists of morphisms

      f   π
    X ⇉ Y → Z
      g

satisfying `f ≫ π = g ≫ π` together with morphisms

      t   s
    X ← Y ← Z

satisfying `s ≫ π = 𝟙 Z`, `t ≫ g = 𝟙 Y` and `t ≫ f = π ≫ s`.

The name "coequalizer" is appropriate, since any split coequalizer is a coequalizer, see
`category_theory.is_split_coequalizer.is_coequalizer`.
Split coequalizers are also absolute, since a functor preserves all the structure above.
-/
structure is_split_coequalizer {Z : C} (π : Y ⟶ Z) :=
(right_section : Z ⟶ Y)
(left_section : Y ⟶ X)
(condition : f ≫ π = g ≫ π)
(right_section_π : right_section ≫ π = 𝟙 Z)
(left_section_bottom : left_section ≫ g = 𝟙 Y)
(left_section_top : left_section ≫ f = π ≫ right_section)

instance {X : C} : inhabited (is_split_coequalizer (𝟙 X) (𝟙 X) (𝟙 X)) :=
⟨⟨𝟙 _, 𝟙 _, rfl, category.id_comp _, category.id_comp _, rfl⟩⟩

open is_split_coequalizer
attribute [reassoc] condition
attribute [simp, reassoc] right_section_π left_section_bottom left_section_top

variables {f g}

/-- Split coequalizers are absolute: they are preserved by any functor. -/
@[simps]
def is_split_coequalizer.map {Z : C} {π : Y ⟶ Z} (q : is_split_coequalizer f g π) (F : C ⥤ D) :
  is_split_coequalizer (F.map f) (F.map g) (F.map π) :=
{ right_section := F.map q.right_section,
  left_section := F.map q.left_section,
  condition := by rw [←F.map_comp, q.condition, F.map_comp],
  right_section_π := by rw [←F.map_comp, q.right_section_π, F.map_id],
  left_section_bottom := by rw [←F.map_comp, q.left_section_bottom, F.map_id],
  left_section_top := by rw [←F.map_comp, q.left_section_top, F.map_comp] }

section

open limits

/-- A split coequalizer clearly induces a cofork. -/
@[simps]
def is_split_coequalizer.as_cofork {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) :
  cofork f g :=
cofork.of_π h t.condition

/--
The cofork induced by a split coequalizer is a coequalizer, justifying the name. In some cases it
is more convenient to show a given cofork is a coequalizer by showing it is split.
-/
def is_split_coequalizer.is_coequalizer
  {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) :
  is_colimit t.as_cofork :=
cofork.is_colimit.mk' _ $ λ s,
⟨t.right_section ≫ s.π,
 by { dsimp, rw [← t.left_section_top_assoc, s.condition, t.left_section_bottom_assoc] },
 λ m hm, by { simp [←hm] }⟩

end

variables (f g)
/--
The pair `f,g` is a split pair if there is a `h : Y ⟶ Z` so that `f, g, h` forms a split coequalizer
in `C`.
-/
class has_split_coequalizer : Prop :=
(splittable [] : ∃ {Z : C} (h : Y ⟶ Z), nonempty (is_split_coequalizer f g h))

/--
The pair `f,g` is a `G`-split pair if there is a `h : G Y ⟶ Z` so that `G f, G g, h` forms a split
coequalizer in `D`.
-/
abbreviation functor.is_split_pair : Prop := has_split_coequalizer (G.map f) (G.map g)

/-- Get the coequalizer object from the typeclass `is_split_pair`. -/
noncomputable def has_split_coequalizer.coequalizer_of_split [has_split_coequalizer f g] : C :=
(has_split_coequalizer.splittable f g).some

/-- Get the coequalizer morphism from the typeclass `is_split_pair`. -/
noncomputable def has_split_coequalizer.coequalizer_π [has_split_coequalizer f g] :
  Y ⟶ has_split_coequalizer.coequalizer_of_split f g :=
(has_split_coequalizer.splittable f g).some_spec.some

/-- The coequalizer morphism `coequalizer_ι` gives a split coequalizer on `f,g`. -/
noncomputable def has_split_coequalizer.is_split_coequalizer [has_split_coequalizer f g] :
  is_split_coequalizer f g (has_split_coequalizer.coequalizer_π f g) :=
classical.choice (has_split_coequalizer.splittable f g).some_spec.some_spec

/-- If `f, g` is split, then `G f, G g` is split. -/
instance map_is_split_pair [has_split_coequalizer f g] :
  has_split_coequalizer (G.map f) (G.map g) :=
{ splittable :=
  ⟨_, _, ⟨is_split_coequalizer.map (has_split_coequalizer.is_split_coequalizer f g) _⟩⟩ }

namespace limits

/-- If a pair has a split coequalizer, it has a coequalizer. -/
@[priority 1]
instance has_coequalizer_of_has_split_coequalizer [has_split_coequalizer f g] :
  has_coequalizer f g :=
has_colimit.mk ⟨_, (has_split_coequalizer.is_split_coequalizer f g).is_coequalizer⟩

end limits

end category_theory

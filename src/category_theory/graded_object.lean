/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.shift
import category_theory.concrete_category

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We define the category structure on these.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `graded_object β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `graded_object β C`.
-/

open category_theory.limits

namespace category_theory

universes w v u

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
def graded_object (β : Type w) (C : Type u) : Type (max w u) := β → C

-- Satisfying the inhabited linter...
instance inhabited_graded_object (β : Type w) (C : Type u) [inhabited C] :
  inhabited (graded_object β C) :=
⟨λ b, inhabited.default C⟩

/--
A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
@[nolint unused_arguments] -- `s` is here to distinguish type synonyms asking for different shifts
abbreviation graded_object_with_shift {β : Type w} [add_comm_group β] (s : β) (C : Type u) : Type (max w u) := graded_object β C

namespace graded_object

variables {C : Type u} [category.{v} C]

instance category_of_graded_objects (β : Type w) : category.{(max w v)} (graded_object β C) :=
{ hom := λ X Y, Π b : β, X b ⟶ Y b,
  id := λ X b, 𝟙 (X b),
  comp := λ X Y Z f g b, f b ≫ g b, }

@[simp]
lemma id_apply {β : Type w} (X : graded_object β C) (b : β) :
  ((𝟙 X) : Π b, X b ⟶ X b) b = 𝟙 (X b) := rfl

@[simp]
lemma comp_apply {β : Type w} {X Y Z : graded_object β C} (f : X ⟶ Y) (g : Y ⟶ Z) (b : β) :
  ((f ≫ g) : Π b, X b ⟶ Z b) b = f b ≫ g b := rfl

section
variable (C)

/-- Pull back a graded object along a change-of-grading function. -/
@[simps]
def comap {β γ : Type w} (f : β → γ) :
  (graded_object γ C) ⥤ (graded_object β C) :=
{ obj := λ X, X ∘ f,
  map := λ X Y g b, g (f b) }

/--
The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
def comap_id (β : Type w) : comap C (id : β → β) ≅ 𝟭 (graded_object β C) :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }.

/--
The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps]
def comap_comp {β γ δ : Type w} (f : β → γ) (g : γ → δ) : comap C g ⋙ comap C f ≅ comap C (g ∘ f) :=
{ hom := { app := λ X b, 𝟙 (X (g (f b))) },
  inv := { app := λ X b, 𝟙 (X (g (f b))) } }

/--
The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
def comap_eq {β γ : Type w} {f g : β → γ} (h : f = g) : comap C f ≅ comap C g :=
{ hom := { app := λ X b, eq_to_hom begin dsimp [comap], subst h, end },
  inv := { app := λ X b, eq_to_hom begin dsimp [comap], subst h, end }, }

@[simp]
lemma comap_eq_symm {β γ : Type w} {f g : β → γ} (h : f = g) : comap_eq C h.symm = (comap_eq C h).symm :=
by tidy

@[simp]
lemma comap_eq_trans {β γ : Type w} {f g h : β → γ} (k : f = g) (l : g = h) :
  comap_eq C (k.trans l) = comap_eq C k ≪≫ comap_eq C l :=
begin
  ext X b,
  simp,
end

/--
The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
def comap_equiv {β γ : Type w} (e : β ≃ γ) :
  (graded_object β C) ≌ (graded_object γ C) :=
{ functor := comap C (e.symm : γ → β),
  inverse := comap C (e : β → γ),
  counit_iso := (comap_comp C _ _).trans (comap_eq C (by { ext, simp } )),
  unit_iso := (comap_eq C (by { ext, simp} )).trans (comap_comp _ _ _).symm,
  functor_unit_iso_comp' := λ X, begin ext b, dsimp, simp, end, }

end

instance has_shift {β : Type} [add_comm_group β] (s : β) : has_shift (graded_object_with_shift s C) :=
{ shift := comap_equiv C
  { to_fun := λ b, b-s,
    inv_fun := λ b, b+s,
    left_inv := λ x, (by simp),
    right_inv := λ x, (by simp), } }

instance has_zero_morphisms [has_zero_morphisms C] (β : Type w) :
  has_zero_morphisms.{(max w v)} (graded_object β C) :=
{ has_zero := λ X Y,
  { zero := λ b, 0 } }

@[simp]
lemma zero_apply [has_zero_morphisms C] (β : Type w) (X Y : graded_object β C) (b : β) :
  (0 : X ⟶ Y) b = 0 := rfl

section
local attribute [instance] has_zero_object.has_zero

instance has_zero_object [has_zero_object C] [has_zero_morphisms C] (β : Type w) :
  has_zero_object.{(max w v)} (graded_object β C) :=
{ zero := λ b, (0 : C),
  unique_to := λ X, ⟨⟨λ b, 0⟩, λ f, (by ext)⟩,
  unique_from := λ X, ⟨⟨λ b, 0⟩, λ f, (by ext)⟩, }
end

end graded_object

namespace graded_object
-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.
-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.
-- If you're grading by things in higher universes, have fun!
variables (β : Type)
variables (C : Type u) [category.{v} C]
variables [has_coproducts C]

/--
The total object of a graded object is the coproduct of the graded components.
-/
def total : graded_object β C ⥤ C :=
{ obj := λ X, ∐ (λ i : ulift.{v} β, X i.down),
  map := λ X Y f, limits.sigma.map (λ i, f i.down) }.

variables [has_zero_morphisms C]

/--
The `total` functor taking a graded object to the coproduct of its graded components is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms and decidable equality for the grading.
-/
instance : faithful (total β C) :=
{ map_injective' := λ X Y f g w,
  begin
    classical,
    ext i,
    replace w := sigma.ι (λ i : ulift β, X i.down) ⟨i⟩ ≫= w,
    erw [colimit.ι_map, colimit.ι_map] at w,
    exact mono.right_cancellation _ _ w,
  end }

end graded_object

namespace graded_object

variables (β : Type)
variables (C : Type (u+1)) [large_category C] [concrete_category C]
  [has_coproducts C] [has_zero_morphisms C]

instance : concrete_category (graded_object β C) :=
{ forget := total β C ⋙ forget C }

instance : has_forget₂ (graded_object β C) C :=
{ forget₂ := total β C }

end graded_object

end category_theory

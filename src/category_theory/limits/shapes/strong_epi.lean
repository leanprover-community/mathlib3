/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.arrow
import category_theory.balanced

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`, such
that for every commutative square with `f` at the top and a monomorphism at the bottom, there is
a diagonal morphism making the two triangles commute. This lift is necessarily unique (as shown in
`comma.lean`).

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

We also define classes `strong_mono_category` and `strong_epi_category` for categories in which
every monomorphism or epimorphism is strong, and deduce that these categories are balanced.

## TODO

Show that the dual of a strong epimorphism is a strong monomorphism, and vice versa.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

variables {P Q : C}

/-- A strong epimorphism `f` is an epimorphism such that every commutative square with `f` at the
    top and a monomorphism at the bottom has a lift. -/
class strong_epi (f : P ⟶ Q) : Prop :=
(epi : epi f)
(has_lift : Π {X Y : C} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y} [mono z] (h : u ≫ z = f ≫ v),
  arrow.has_lift $ arrow.hom_mk' h)

/-- A strong monomorphism `f` is a monomorphism such that every commutative square with `f` at the
    bottom and an epimorphism at the top has a lift. -/
class strong_mono (f : P ⟶ Q) : Prop :=
(mono : mono f)
(has_lift : Π {X Y : C} {u : X ⟶ P} {v : Y ⟶ Q} {z : X ⟶ Y} [epi z] (h : u ≫ f = z ≫ v),
  arrow.has_lift $ arrow.hom_mk' h)

attribute [instance] strong_epi.has_lift
attribute [instance] strong_mono.has_lift

@[priority 100]
instance epi_of_strong_epi (f : P ⟶ Q) [strong_epi f] : epi f := strong_epi.epi

@[priority 100]
instance mono_of_strong_mono (f : P ⟶ Q) [strong_mono f] : mono f := strong_mono.mono

section
variables {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
lemma strong_epi_comp [strong_epi f] [strong_epi g] : strong_epi (f ≫ g) :=
{ epi := epi_comp _ _,
  has_lift :=
  begin
    introsI,
    have h₀ : u ≫ z = f ≫ g ≫ v, by simpa [category.assoc] using h,
    let w : Q ⟶ X := arrow.lift (arrow.hom_mk' h₀),
    have h₁ : w ≫ z = g ≫ v, by rw arrow.lift_mk'_right,
    exact arrow.has_lift.mk ⟨(arrow.lift (arrow.hom_mk' h₁) : R ⟶ X), by simp, by simp⟩
  end }

/-- The composition of two strong monomorphisms is a strong monomorphism. -/
lemma strong_mono_comp [strong_mono f] [strong_mono g] : strong_mono (f ≫ g) :=
{ mono := mono_comp _ _,
  has_lift :=
  begin
    introsI,
    have h₀ : (u ≫ f) ≫ g = z ≫ v, by simpa [category.assoc] using h,
    let w : Y ⟶ Q := arrow.lift (arrow.hom_mk' h₀),
    have h₁ : u ≫ f = z ≫ w, by rw arrow.lift_mk'_left,
    exact arrow.has_lift.mk ⟨(arrow.lift (arrow.hom_mk' h₁) : Y ⟶ P), by simp, by simp⟩
  end }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
lemma strong_epi_of_strong_epi [strong_epi (f ≫ g)] : strong_epi g :=
{ epi := epi_of_epi f g,
  has_lift :=
  begin
    introsI,
    have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v, by simp only [category.assoc, h],
    exact arrow.has_lift.mk
      ⟨(arrow.lift (arrow.hom_mk' h₀) : R ⟶ X), (cancel_mono z).1 (by simp [h]), by simp⟩,
  end }

/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/
lemma strong_mono_of_strong_mono [strong_mono (f ≫ g)] : strong_mono f :=
{ mono := mono_of_mono f g,
  has_lift :=
  begin
    introsI,
    have h₀ : u ≫ f ≫ g = z ≫ v ≫ g, by rw reassoc_of h,
    exact arrow.has_lift.mk
      ⟨(arrow.lift (arrow.hom_mk' h₀) : Y ⟶ P), by simp, (cancel_epi z).1 (by simp [h])⟩
  end }

/-- An isomorphism is in particular a strong epimorphism. -/
@[priority 100] instance strong_epi_of_is_iso [is_iso f] : strong_epi f :=
{ epi := by apply_instance,
  has_lift := λ X Y u v z _ h, arrow.has_lift.mk ⟨inv f ≫ u, by simp, by simp [h]⟩ }

/-- An isomorphism is in particular a strong monomorphism. -/
@[priority 100] instance strong_mono_of_is_iso [is_iso f] : strong_mono f :=
{ mono := by apply_instance,
  has_lift := λ X Y u v z _ h, arrow.has_lift.mk
    ⟨v ≫ inv f, by simp [← category.assoc, ← h], by simp⟩ }

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
lemma is_iso_of_mono_of_strong_epi (f : P ⟶ Q) [mono f] [strong_epi f] : is_iso f :=
⟨⟨arrow.lift $ arrow.hom_mk' $ show 𝟙 P ≫ f = f ≫ 𝟙 Q, by simp, by tidy⟩⟩

/-- A strong monomorphism that is an epimorphism is an isomorphism. -/
lemma is_iso_of_epi_of_strong_mono (f : P ⟶ Q) [epi f] [strong_mono f] : is_iso f :=
⟨⟨arrow.lift $ arrow.hom_mk' $ show 𝟙 P ≫ f = f ≫ 𝟙 Q, by simp, by tidy⟩⟩

section
variables (C)

/-- A strong epi category is a category in which every epimorphism is strong. -/
class strong_epi_category : Prop :=
(strong_epi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [epi f], strong_epi f)

/-- A strong mono category is a category in which every monomorphism is strong. -/
class strong_mono_category : Prop :=
(strong_mono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [mono f], strong_mono f)

end

lemma strong_epi_of_epi [strong_epi_category C] (f : P ⟶ Q) [epi f] : strong_epi f :=
strong_epi_category.strong_epi_of_epi _

lemma strong_mono_of_mono [strong_mono_category C] (f : P ⟶ Q) [mono f] : strong_mono f :=
strong_mono_category.strong_mono_of_mono _

section
local attribute [instance] strong_epi_of_epi

@[priority 100]
instance balanced_of_strong_epi_category [strong_epi_category C] : balanced C :=
{ is_iso_of_mono_of_epi := λ _ _ _ _ _, by exactI is_iso_of_mono_of_strong_epi _ }

end

section
local attribute [instance] strong_mono_of_mono

@[priority 100]
instance balanced_of_strong_mono_category [strong_mono_category C] : balanced C :=
{ is_iso_of_mono_of_epi := λ _ _ _ _ _, by exactI is_iso_of_epi_of_strong_mono _ }

end

end category_theory

/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.balanced
import category_theory.lifting_properties.basic

/-!
# Strong epimorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`
which has the (unique) left lifting property with respect to monomorphisms. Similarly,
a strong monomorphisms in a monomorphism which has the (unique) right lifting property
with respect to epimorphisms.

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

/-- A strong epimorphism `f` is an epimorphism which has the left lifting property
with respect to monomorphisms. -/
class strong_epi (f : P ⟶ Q) : Prop :=
(epi : epi f)
(llp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [mono z], has_lifting_property f z)

lemma strong_epi.mk' {f : P ⟶ Q} [epi f]
  (hf : ∀ (X Y : C) (z : X ⟶ Y) (hz : mono z) (u : P ⟶ X) (v : Q ⟶ Y)
    (sq : comm_sq u f z v), sq.has_lift) : strong_epi f :=
{ epi := infer_instance,
  llp := λ X Y z hz, ⟨λ u v sq, hf X Y z hz u v sq⟩, }

/-- A strong monomorphism `f` is a monomorphism which has the right lifting property
with respect to epimorphisms. -/
class strong_mono (f : P ⟶ Q) : Prop :=
(mono : mono f)
(rlp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [epi z], has_lifting_property z f)

lemma strong_mono.mk' {f : P ⟶ Q} [mono f]
  (hf : ∀ (X Y : C) (z : X ⟶ Y) (hz : epi z) (u : X ⟶ P) (v : Y ⟶ Q)
    (sq : comm_sq u z f v), sq.has_lift) : strong_mono f :=
{ mono := infer_instance,
  rlp := λ X Y z hz, ⟨λ u v sq, hf X Y z hz u v sq⟩, }

attribute [instance, priority 100] strong_epi.llp
attribute [instance, priority 100] strong_mono.rlp

@[priority 100]
instance epi_of_strong_epi (f : P ⟶ Q) [strong_epi f] : epi f := strong_epi.epi

@[priority 100]
instance mono_of_strong_mono (f : P ⟶ Q) [strong_mono f] : mono f := strong_mono.mono

section
variables {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
lemma strong_epi_comp [strong_epi f] [strong_epi g] : strong_epi (f ≫ g) :=
{ epi := epi_comp _ _,
  llp := by { introsI, apply_instance, }, }

/-- The composition of two strong monomorphisms is a strong monomorphism. -/
lemma strong_mono_comp [strong_mono f] [strong_mono g] : strong_mono (f ≫ g) :=
{ mono := mono_comp _ _,
  rlp := by { introsI, apply_instance, }, }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
lemma strong_epi_of_strong_epi [strong_epi (f ≫ g)] : strong_epi g :=
{ epi := epi_of_epi f g,
  llp := begin
    introsI,
    constructor,
    intros u v sq,
    have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v, by simp only [category.assoc, sq.w],
    exact comm_sq.has_lift.mk' ⟨(comm_sq.mk h₀).lift,
      by simp only [← cancel_mono z, category.assoc, comm_sq.fac_right, sq.w], by simp⟩,
  end, }

/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/
lemma strong_mono_of_strong_mono [strong_mono (f ≫ g)] : strong_mono f :=
{ mono := mono_of_mono f g,
  rlp := begin
    introsI,
    constructor,
    intros u v sq,
    have h₀ : u ≫ f ≫ g = z ≫ v ≫ g, by rw reassoc_of sq.w,
    exact comm_sq.has_lift.mk' ⟨(comm_sq.mk h₀).lift, by simp, by simp [← cancel_epi z, sq.w]⟩,
  end, }

/-- An isomorphism is in particular a strong epimorphism. -/
@[priority 100] instance strong_epi_of_is_iso [is_iso f] : strong_epi f :=
{ epi := by apply_instance,
  llp := λ X Y z hz, has_lifting_property.of_left_iso _ _, }

/-- An isomorphism is in particular a strong monomorphism. -/
@[priority 100] instance strong_mono_of_is_iso [is_iso f] : strong_mono f :=
{ mono := by apply_instance,
  rlp := λ X Y z hz, has_lifting_property.of_right_iso _ _, }

lemma strong_epi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  (e : arrow.mk f ≅ arrow.mk g) [h : strong_epi f] : strong_epi g :=
{ epi := begin
    rw arrow.iso_w' e,
    haveI := epi_comp f e.hom.right,
    apply epi_comp,
  end,
  llp := λ X Y z, by { introI, apply has_lifting_property.of_arrow_iso_left e z, }, }

lemma strong_mono.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  (e : arrow.mk f ≅ arrow.mk g) [h : strong_mono f] : strong_mono g :=
{ mono := begin
    rw arrow.iso_w' e,
    haveI := mono_comp f e.hom.right,
    apply mono_comp,
  end,
  rlp := λ X Y z, by { introI, apply has_lifting_property.of_arrow_iso_right z e, }, }

lemma strong_epi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  (e : arrow.mk f ≅ arrow.mk g) : strong_epi f ↔ strong_epi g :=
by { split; introI, exacts [strong_epi.of_arrow_iso e, strong_epi.of_arrow_iso e.symm], }

lemma strong_mono.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  (e : arrow.mk f ≅ arrow.mk g) : strong_mono f ↔ strong_mono g :=
by { split; introI, exacts [strong_mono.of_arrow_iso e, strong_mono.of_arrow_iso e.symm], }

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
lemma is_iso_of_mono_of_strong_epi (f : P ⟶ Q) [mono f] [strong_epi f] : is_iso f :=
⟨⟨(comm_sq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q, by simp)).lift, by tidy⟩⟩

/-- A strong monomorphism that is an epimorphism is an isomorphism. -/
lemma is_iso_of_epi_of_strong_mono (f : P ⟶ Q) [epi f] [strong_mono f] : is_iso f :=
⟨⟨(comm_sq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q, by simp)).lift, by tidy⟩⟩

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

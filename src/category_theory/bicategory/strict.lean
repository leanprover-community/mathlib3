/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.eq_to_hom
import category_theory.bicategory.basic

/-!
# Strict bicategories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A bicategory is called `strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.

## Implementation notes

In the literature of category theory, a strict bicategory (usually called a strict 2-category) is
often defined as a bicategory whose left unitors, right unitors, and associators are identities.
We cannot use this definition directly here since the types of 2-morphisms depend on 1-morphisms.
For this reason, we use `eq_to_iso`, which gives isomorphisms from equalities, instead of
identities.
-/

namespace category_theory

open_locale bicategory

universes w v u

variables (B : Type u) [bicategory.{w v} B]

/--
A bicategory is called `strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.
-/
class bicategory.strict : Prop :=
(id_comp' : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f . obviously)
(comp_id' : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f . obviously)
(assoc' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  (f ≫ g) ≫ h = f ≫ (g ≫ h) . obviously)
(left_unitor_eq_to_iso' : ∀ {a b : B} (f : a ⟶ b),
  λ_ f = eq_to_iso (id_comp' f) . obviously)
(right_unitor_eq_to_iso' : ∀ {a b : B} (f : a ⟶ b),
  ρ_ f = eq_to_iso (comp_id' f) . obviously)
(associator_eq_to_iso' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  α_ f g h = eq_to_iso (assoc' f g h) . obviously)

restate_axiom bicategory.strict.id_comp'
restate_axiom bicategory.strict.comp_id'
restate_axiom bicategory.strict.assoc'
restate_axiom bicategory.strict.left_unitor_eq_to_iso'
restate_axiom bicategory.strict.right_unitor_eq_to_iso'
restate_axiom bicategory.strict.associator_eq_to_iso'
attribute [simp]
  bicategory.strict.id_comp bicategory.strict.left_unitor_eq_to_iso
  bicategory.strict.comp_id bicategory.strict.right_unitor_eq_to_iso
  bicategory.strict.assoc bicategory.strict.associator_eq_to_iso

/-- Category structure on a strict bicategory -/
@[priority 100] -- see Note [lower instance priority]
instance strict_bicategory.category [bicategory.strict B] : category B :=
{ id_comp' := λ a b, bicategory.strict.id_comp,
  comp_id' := λ a b, bicategory.strict.comp_id,
  assoc' := λ a b c d, bicategory.strict.assoc }

namespace bicategory

variables {B}

@[simp]
lemma whisker_left_eq_to_hom {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g = h) :
  f ◁ eq_to_hom η = eq_to_hom (congr_arg2 (≫) rfl η) :=
by { cases η, simp only [whisker_left_id, eq_to_hom_refl] }

@[simp]
lemma eq_to_hom_whisker_right {a b c : B} {f g : a ⟶ b} (η : f = g) (h : b ⟶ c) :
  eq_to_hom η ▷ h = eq_to_hom (congr_arg2 (≫) η rfl) :=
by { cases η, simp only [id_whisker_right, eq_to_hom_refl] }

end bicategory

end category_theory

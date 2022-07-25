/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.pullbacks

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `stable_under_base_change`: `P` is stable under base change if `P (Y ⟶ S) → P (X ×[S] Y ⟶ X)`.

-/

universes v u

open category_theory category_theory.limits opposite

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- A `morphism_property C` is a class of morphisms between objects in `C`. -/
@[derive complete_lattice]
def morphism_property := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Prop

instance : inhabited (morphism_property C) := ⟨⊤⟩

variable {C}

namespace morphism_property

/-- A morphism property `respects_iso` if it still holds when composed with an isomorphism -/
def respects_iso (P : morphism_property C) : Prop :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f)) ∧
  (∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.hom))

/-- A morphism property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def stable_under_composition (P : morphism_property C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)

/-- A morphism property is `stable_under_composition` if the base change of such a morphism
still falls in the class. -/
def stable_under_base_change [has_pullbacks C] (P : morphism_property C) : Prop :=
∀ ⦃X Y S : C⦄ (f : X ⟶ S) (g : Y ⟶ S), P g → P (pullback.fst : pullback f g ⟶ X)

lemma stable_under_composition.respects_iso {P : morphism_property C}
  (hP : stable_under_composition P) (hP' : ∀ {X Y} (e : X ≅ Y), P e.hom) : respects_iso P :=
⟨λ X Y Z e f hf, hP _ _ (hP' e) hf, λ X Y Z e f hf, hP _ _ hf (hP' e)⟩

lemma respects_iso.cancel_left_is_iso {P : morphism_property C}
  (hP : respects_iso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] :
    P (f ≫ g) ↔ P g :=
⟨λ h, by simpa using hP.1 (as_iso f).symm (f ≫ g) h, hP.1 (as_iso f) g⟩

lemma respects_iso.cancel_right_is_iso {P : morphism_property C}
  (hP : respects_iso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
    P (f ≫ g) ↔ P f :=
⟨λ h, by simpa using hP.2 (as_iso g).symm (f ≫ g) h, hP.2 (as_iso g) f⟩

-- This is here to mirror `stable_under_base_change.snd`.
@[nolint unused_arguments]
lemma stable_under_base_change.fst [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {X Y S : C} (f : X ⟶ S)
  (g : Y ⟶ S) (H : P g) : P (pullback.fst : pullback f g ⟶ X) :=
hP f g H

lemma stable_under_base_change.snd [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {X Y S : C} (f : X ⟶ S)
  (g : Y ⟶ S) (H : P f) : P (pullback.snd : pullback f g ⟶ Y) :=
begin
  rw [← pullback_symmetry_hom_comp_fst, hP'.cancel_left_is_iso],
  exact hP g f H
end

lemma stable_under_base_change.base_change_obj [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {S S' : C} (f : S' ⟶ S)
  (X : over S) (H : P X.hom) : P ((base_change f).obj X).hom :=
hP.snd hP' X.hom f H

lemma stable_under_base_change.base_change_map [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {S S' : C} (f : S' ⟶ S)
  {X Y : over S} (g : X ⟶ Y) (H : P g.left) : P ((base_change f).map g).left :=
begin
  let e := pullback_right_pullback_fst_iso Y.hom f g.left ≪≫
    pullback.congr_hom (g.w.trans (category.comp_id _)) rfl,
  have : e.inv ≫ pullback.snd = ((base_change f).map g).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw [← this, hP'.cancel_left_is_iso],
  apply hP.snd hP',
  exact H
end

lemma stable_under_base_change.pullback_map [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : respects_iso P)
  (hP'' : stable_under_composition P) {S X X' Y Y' : C}
  {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'}
  (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _)
      ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂)) :=
begin
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _)
    ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂) =
      ((pullback_symmetry _ _).hom ≫
      ((base_change _).map (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g')).left) ≫
      (pullback_symmetry _ _).hom ≫
      ((base_change g').map (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f')).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw this,
  apply hP''; rw hP'.cancel_left_is_iso,
  exacts [hP.base_change_map hP' _ (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g') h₂,
    hP.base_change_map hP' _ (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f') h₁],
end

end morphism_property

end category_theory

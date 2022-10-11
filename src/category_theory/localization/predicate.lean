/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.construction

/-!

# Predicate for localized categories

In this file, a predicate `L.is_localization W` is introduced for a functor `L : C ⥤ D`
and `W : morphism_property C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `strict_universal_property_fixed_target L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factors as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `is_localization.mk'` for `L.is_localization W`.

-/

noncomputable theory

namespace category_theory

variables {C D : Type*} [category C] [category D]
  (L : C ⥤ D) (W : morphism_property C)
  (E : Type*) [category E]

namespace functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : morphism_property C`. -/
class is_localization : Prop :=
(inverts : W.is_inverted_by L)
(nonempty_is_equivalence : nonempty (is_equivalence (localization.construction.lift L inverts)))

instance Q_is_localization : W.Q.is_localization W :=
{ inverts := W.Q_inverts,
  nonempty_is_equivalence := begin
    suffices : localization.construction.lift W.Q W.Q_inverts = 𝟭 _,
    { apply nonempty.intro, rw this, apply_instance, },
    apply localization.construction.uniq,
    simpa only [localization.construction.fac],
  end, }

end functor

namespace localization

/-- This universal property states that a functor `L : C ⥤ D` inverts morphisms
in `W` and the all functors `D ⥤ E` (for a fixed category `E`) uniquely factors
through `L`. -/
structure strict_universal_property_fixed_target :=
(inverts : W.is_inverted_by L)
(lift : Π (F : C ⥤ E) (hF : W.is_inverted_by F), D ⥤ E)
(fac : Π (F : C ⥤ E) (hF : W.is_inverted_by F), L ⋙ lift F hF = F)
(uniq : Π (F₁ F₂ : D ⥤ E) (h : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂)

/-- The localized category `W.localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
def strict_universal_property_fixed_target_Q :
  strict_universal_property_fixed_target W.Q W E :=
{ inverts := W.Q_inverts,
  lift := construction.lift,
  fac := construction.fac,
  uniq := construction.uniq, }

instance : inhabited (strict_universal_property_fixed_target W.Q W E) :=
⟨strict_universal_property_fixed_target_Q _ _⟩

/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
def strict_universal_property_fixed_target_id (hW : W ⊆ morphism_property.isomorphisms C):
  strict_universal_property_fixed_target (𝟭 C) W E :=
{ inverts := λ X Y f hf, hW f hf,
  lift := λ F hF, F,
  fac := λ F hF, by { cases F, refl, },
  uniq := λ F₁ F₂ eq, by { cases F₁, cases F₂, exact eq, }, }

end localization

namespace functor

lemma is_localization.mk'
  (h₁ : localization.strict_universal_property_fixed_target L W D)
  (h₂ : localization.strict_universal_property_fixed_target L W W.localization) :
  is_localization L W :=
{ inverts := h₁.inverts,
  nonempty_is_equivalence := nonempty.intro
  { inverse := h₂.lift W.Q W.Q_inverts,
    unit_iso := eq_to_iso (localization.construction.uniq _ _
      (by simp only [← functor.assoc, localization.construction.fac, h₂.fac, functor.comp_id])),
    counit_iso := eq_to_iso (h₁.uniq _ _ (by simp only [← functor.assoc, h₂.fac,
      localization.construction.fac, functor.comp_id])),
    functor_unit_iso_comp' := λ X, by simpa only [eq_to_iso.hom, eq_to_hom_app,
      eq_to_hom_map, eq_to_hom_trans, eq_to_hom_refl], }, }

lemma is_localization.for_id (hW : W ⊆ morphism_property.isomorphisms C):
  (𝟭 C).is_localization W :=
is_localization.mk' _ _
  (localization.strict_universal_property_fixed_target_id W _ hW)
  (localization.strict_universal_property_fixed_target_id W _ hW)

end functor

namespace localization

variable [L.is_localization W]
include L W

lemma inverts : W.is_inverted_by L := (infer_instance : L.is_localization W).inverts

variable {W}

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.is_localization W`. -/
@[simps]
def iso_of_hom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
by { haveI : is_iso (L.map f) := inverts L W f hf, exact as_iso (L.map f), }

variable (W)

instance : is_equivalence (localization.construction.lift L (inverts L W)) :=
(infer_instance : L.is_localization W).nonempty_is_equivalence.some

/-- A chosen equivalence of categories `W.localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.is_localization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`. -/
def equivalence_from_model : W.localization ≌ D :=
(localization.construction.lift L (inverts L W)).as_equivalence

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `W.Q` and `L`. -/
def Q_comp_equivalence_from_model_functor_iso :
  W.Q ⋙ (equivalence_from_model L W).functor ≅ L := eq_to_iso (construction.fac _ _)

/-- Via the equivalence of categories `equivalence_from_model L W : W.localization ≌ D`,
one may identify the functors `L` and `W.Q`. -/
def comp_equivalence_from_model_inverse_iso :
  L ⋙ (equivalence_from_model L W).inverse ≅ W.Q :=
calc L ⋙ (equivalence_from_model L W).inverse ≅ _ :
  iso_whisker_right (Q_comp_equivalence_from_model_functor_iso L W).symm _
... ≅ W.Q ⋙ ((equivalence_from_model L W).functor ⋙ (equivalence_from_model L W).inverse) :
  functor.associator _ _ _
... ≅ W.Q ⋙ 𝟭 _ : iso_whisker_left _ ((equivalence_from_model L W).unit_iso.symm)
... ≅ W.Q : functor.right_unitor _

lemma ess_surj : ess_surj L :=
⟨λ X, ⟨(construction.obj_equiv W).inv_fun ((equivalence_from_model L W).inverse.obj X),
  nonempty.intro ((Q_comp_equivalence_from_model_functor_iso L W).symm.app _ ≪≫
  (equivalence_from_model L W).counit_iso.app X)⟩⟩

end localization

end category_theory

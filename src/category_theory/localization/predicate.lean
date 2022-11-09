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

When `L : C ⥤ D` is a localization functor for `W : morphism_property` (i.e. when
`[L.is_localization W]` holds), for any category `E`, there is
an equivalence `functor_equivalence L W E : (D ⥤ E) ≌ (W.functors_inverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `lifting L W F F'`. The functions
`lift_nat_trans` and `lift_nat_iso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/

noncomputable theory

namespace category_theory

open category

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

lemma inverts : W.is_inverted_by L := (infer_instance : L.is_localization W).inverts

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.is_localization W`. -/
@[simps]
def iso_of_hom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
by { haveI : is_iso (L.map f) := inverts L W f hf, exact as_iso (L.map f), }

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

/-- The functor `(D ⥤ E) ⥤ W.functors_inverting E` induced by the composition
with a localization functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
def whiskering_left_functor : (D ⥤ E) ⥤ W.functors_inverting E :=
full_subcategory.lift _ ((whiskering_left _ _ E).obj L)
  (morphism_property.is_inverted_by.of_comp W L (inverts L W ))

instance : is_equivalence (whiskering_left_functor L W E) :=
begin
  refine is_equivalence.of_iso _ (is_equivalence.of_equivalence
    ((equivalence.congr_left (equivalence_from_model L W).symm).trans
    (construction.whiskering_left_equivalence W E))),
  refine nat_iso.of_components (λ F, eq_to_iso begin
    ext,
    change (W.Q ⋙ (localization.construction.lift L (inverts L W))) ⋙ F = L ⋙ F,
    rw construction.fac,
  end)
  (λ F₁ F₂ τ, begin
    ext X,
    dsimp [equivalence_from_model, whisker_left, construction.whiskering_left_equivalence,
      construction.whiskering_left_equivalence.functor, whiskering_left_functor,
      morphism_property.Q],
    erw [nat_trans.comp_app, nat_trans.comp_app, eq_to_hom_app, eq_to_hom_app,
      eq_to_hom_refl, eq_to_hom_refl, comp_id, id_comp],
    all_goals
    { change (W.Q ⋙ (localization.construction.lift L (inverts L W))) ⋙ _ = L ⋙ _,
      rw construction.fac, },
  end),
end

/-- The equivalence of categories `(D ⥤ E) ≌ (W.functors_inverting E)` induced by
the composition with a localization functor `L : C ⥤ D` with respect to
`W : morphism_property C`. -/
def functor_equivalence : (D ⥤ E) ≌ (W.functors_inverting E) :=
(whiskering_left_functor L W E).as_equivalence

include W

/-- The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : morphism_property C`. -/
@[nolint unused_arguments]
def whiskering_left_functor' :
  (D ⥤ E) ⥤ (C ⥤ E) := (whiskering_left C D E).obj L

lemma whiskering_left_functor'_eq :
  whiskering_left_functor' L W E =
    localization.whiskering_left_functor L W E ⋙ induced_functor _ := rfl

variable {E}

@[simp]
lemma whiskering_left_functor'_obj
  (F : D ⥤ E) : (whiskering_left_functor' L W E).obj F = L ⋙ F := rfl

instance : full (whiskering_left_functor' L W E) :=
by { rw whiskering_left_functor'_eq, apply_instance, }

instance : faithful (whiskering_left_functor' L W E) :=
by { rw whiskering_left_functor'_eq, apply_instance, }

lemma nat_trans_ext {F₁ F₂ : D ⥤ E} (τ τ' : F₁ ⟶ F₂)
  (h : ∀ (X : C), τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' :=
begin
  haveI : category_theory.ess_surj L := ess_surj L W,
  ext Y,
  rw [← cancel_epi (F₁.map (L.obj_obj_preimage_iso Y).hom), τ.naturality, τ'.naturality, h],
end

/-- When `L : C ⥤ D` is a localization functor for `W : morphism_property C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class lifting (F : C ⥤ E) (F' : D ⥤ E) :=
(iso [] : L ⋙ F' ≅ F)

variable {W}

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C` and
a functor `F : C ⥤ E` which inverts `W`, this is a choice of functor
`D ⥤ E` which lifts `F`. -/
def lift (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D) [hL : L.is_localization W] :
  D ⥤ E :=
(functor_equivalence L W E).inverse.obj ⟨F, hF⟩

instance lifting_lift (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D)
  [hL : L.is_localization W] : lifting L W F (lift F hF L) :=
⟨(induced_functor _).map_iso ((functor_equivalence L W E).counit_iso.app ⟨F, hF⟩)⟩

/-- The canonical isomorphism `L ⋙ lift F hF L ≅ F` for any functor `F : C ⥤ E`
which inverts `W`, when `L : C ⥤ D` is a localization functor for `W`. -/
@[simps]
def fac (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D) [hL : L.is_localization W] :
  L ⋙ lift F hF L ≅ F :=
lifting.iso _ W _ _

instance lifting_construction_lift (F : C ⥤ D) (hF : W.is_inverted_by F) :
  lifting W.Q W F (construction.lift F hF) :=
⟨eq_to_iso (construction.fac F hF)⟩

variable (W)

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural transformation `τ : F₁ ⟶ F₂` uniquely lifts to a natural transformation `F₁' ⟶ F₂'`. -/
def lift_nat_trans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [lifting L W F₁ F₁']
  [h₂ : lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
(whiskering_left_functor' L W E).preimage
  ((lifting.iso L W F₁ F₁').hom ≫ τ ≫ (lifting.iso L W F₂ F₂').inv)

@[simp]
lemma lift_nat_trans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [lifting L W F₁ F₁']
  [lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) (X : C) :
  (lift_nat_trans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
    (lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ ((lifting.iso L W F₂ F₂')).inv.app X :=
congr_app (functor.image_preimage (whiskering_left_functor' L W E) _) X

@[simp, reassoc]
lemma comp_lift_nat_trans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E)
  [h₁ : lifting L W F₁ F₁'] [h₂ : lifting L W F₂ F₂'] [h₃ : lifting L W F₃ F₃']
  (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
  lift_nat_trans L W F₁ F₂ F₁' F₂' τ ≫ lift_nat_trans L W F₂ F₃ F₂' F₃' τ' =
  lift_nat_trans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
nat_trans_ext L W _ _
  (λ X, by simp only [nat_trans.comp_app, lift_nat_trans_app, assoc, iso.inv_hom_id_app_assoc])

@[simp]
lemma lift_nat_trans_id (F : C ⥤ E) (F' : D ⥤ E) [h : lifting L W F F'] :
  lift_nat_trans L W F F F' F' (𝟙 F) = 𝟙 F' :=
nat_trans_ext L W _ _
  (λ X, by simpa only [lift_nat_trans_app, nat_trans.id_app, id_comp, iso.hom_inv_id_app])

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lifts functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`. -/
@[simps]
def lift_nat_iso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
  [h₁ : lifting L W F₁ F₁'] [h₂ : lifting L W F₂ F₂']
  (e : F₁ ≅ F₂) : F₁' ≅ F₂' :=
{ hom := lift_nat_trans L W F₁ F₂ F₁' F₂' e.hom,
  inv := lift_nat_trans L W F₂ F₁ F₂' F₁' e.inv, }

namespace lifting

@[simps]
instance comp_right {E' : Type*} [category E'] (F : C ⥤ E) (F' : D ⥤ E) [lifting L W F F']
  (G : E ⥤ E') : lifting L W (F ⋙ G) (F' ⋙ G) :=
⟨iso_whisker_right (iso L W F F') G⟩

@[simps]
instance id : lifting L W L (𝟭 D) :=
⟨functor.right_unitor L⟩

/-- Given a localization functor `L : C ⥤ D` for `W : morphism_property C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`.  -/
@[simps]
def of_isos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂')
  [lifting L W F₁ F₁'] : lifting L W F₂ F₂' :=
⟨iso_whisker_left L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩

end lifting

end localization

namespace functor

namespace is_localization

open localization

lemma of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.is_localization W] : L₂.is_localization W :=
begin
  have h := localization.inverts L₁ W,
  rw morphism_property.is_inverted_by.iff_of_iso W e at h,
  let F₁ := localization.construction.lift L₁ (localization.inverts L₁ W),
  let F₂ := localization.construction.lift L₂ h,
  exact
  { inverts := h,
    nonempty_is_equivalence := nonempty.intro
      (is_equivalence.of_iso (lift_nat_iso W.Q W L₁ L₂ F₁ F₂ e) infer_instance), },
end

/-- If `L : C ⥤ D` is a localization for `W : morphism_property C`, then it is also
the case of a functor obtained by post-composing `L` with an equivalence of categories. -/
lemma of_equivalence_target {E : Type*} [category E] (L' : C ⥤ E) (eq : D ≌ E)
  [L.is_localization W] (e : L ⋙ eq.functor ≅ L') : L'.is_localization W :=
begin
  have h : W.is_inverted_by L',
  { rw ← morphism_property.is_inverted_by.iff_of_iso W e,
    exact morphism_property.is_inverted_by.of_comp W L (localization.inverts L W) eq.functor, },
  let F₁ := localization.construction.lift L (localization.inverts L W),
  let F₂ := localization.construction.lift L' h,
  let e' : F₁ ⋙ eq.functor ≅ F₂ := lift_nat_iso W.Q W (L ⋙ eq.functor) L' _ _ e,
  exact
  { inverts := h,
    nonempty_is_equivalence := nonempty.intro (is_equivalence.of_iso e' infer_instance) },
end

end is_localization

end functor

end category_theory

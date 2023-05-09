/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.adjunction.comma
import category_theory.limits.preserves.shapes.terminal
import category_theory.structured_arrow
import category_theory.limits.shapes.equivalence

/-!
# Limits and the category of (co)cones

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files contains results that stem from the limit API. For the definition and the category
instance of `cone`, please refer to `category_theory/limits/cones.lean`.

## Main results
* The category of cones on `F : J ⥤ C` is equivalent to the category
  `costructured_arrow (const J) F`.
* A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
  categories of cones preserves limiting properties.

-/

namespace category_theory.limits

open category_theory category_theory.functor

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {J : Type u₁} [category.{v₁} J] {K : Type u₂} [category.{v₂} K]
variables {C : Type u₃} [category.{v₃} C] {D : Type u₄} [category.{v₄} D]

/-- Construct an object of the category `(Δ ↓ F)` from a cone on `F`. This is part of an
    equivalence, see `cone.equiv_costructured_arrow`. -/
@[simps]
def cone.to_costructured_arrow (F : J ⥤ C) : cone F ⥤ costructured_arrow (const J) F :=
{ obj := λ c, costructured_arrow.mk c.π,
  map := λ c d f, costructured_arrow.hom_mk f.hom $ by { ext, simp } }

/-- Construct a cone on `F` from an object of the category `(Δ ↓ F)`. This is part of an
    equivalence, see `cone.equiv_costructured_arrow`. -/
@[simps]
def cone.from_costructured_arrow (F : J ⥤ C) : costructured_arrow (const J) F ⥤ cone F :=
{ obj := λ c, ⟨c.left, c.hom⟩,
  map := λ c d f,
  { hom := f.left,
    w' := λ j, by { convert (congr_fun (congr_arg nat_trans.app f.w) j), dsimp, simp } } }

/-- The category of cones on `F` is just the comma category `(Δ ↓ F)`, where `Δ` is the constant
    functor. -/
@[simps]
def cone.equiv_costructured_arrow (F : J ⥤ C) : cone F ≌ costructured_arrow (const J) F :=
equivalence.mk (cone.to_costructured_arrow F) (cone.from_costructured_arrow F)
  (nat_iso.of_components cones.eta (by tidy))
  (nat_iso.of_components (λ c, (costructured_arrow.eta _).symm) (by tidy))

/-- A cone is a limit cone iff it is terminal. -/
def cone.is_limit_equiv_is_terminal {F : J ⥤ C} (c : cone F) : is_limit c ≃ is_terminal c :=
is_limit.iso_unique_cone_morphism.to_equiv.trans
{ to_fun := λ h, by exactI is_terminal.of_unique _,
  inv_fun := λ h s, ⟨⟨is_terminal.from h s⟩, λ a, is_terminal.hom_ext h a _⟩,
  left_inv := by tidy,
  right_inv := by tidy }

lemma has_limit_iff_has_terminal_cone (F : J ⥤ C) : has_limit F ↔ has_terminal (cone F) :=
⟨λ h, by exactI (cone.is_limit_equiv_is_terminal _ (limit.is_limit F)).has_terminal,
 λ h, ⟨⟨by exactI ⟨⊤_ _, (cone.is_limit_equiv_is_terminal _).symm terminal_is_terminal⟩⟩⟩⟩

lemma has_limits_of_shape_iff_is_left_adjoint_const :
  has_limits_of_shape J C ↔ nonempty (is_left_adjoint (const J : C ⥤ _)) :=
calc has_limits_of_shape J C
      ↔ ∀ F : J ⥤ C, has_limit F : ⟨λ h, h.has_limit, λ h, by exactI has_limits_of_shape.mk⟩
  ... ↔ ∀ F : J ⥤ C, has_terminal (cone F) : forall_congr has_limit_iff_has_terminal_cone
  ... ↔ ∀ F : J ⥤ C, has_terminal (costructured_arrow (const J) F) :
    forall_congr $ λ F, (cone.equiv_costructured_arrow F).has_terminal_iff
  ... ↔ nonempty (is_left_adjoint (const J : C ⥤ _)) :
    nonempty_is_left_adjoint_iff_has_terminal_costructured_arrow.symm

lemma is_limit.lift_cone_morphism_eq_is_terminal_from {F : J ⥤ C} {c : cone F} (hc : is_limit c)
  (s : cone F) : hc.lift_cone_morphism s =
    is_terminal.from (cone.is_limit_equiv_is_terminal _ hc) _ := rfl

lemma is_terminal.from_eq_lift_cone_morphism {F : J ⥤ C} {c : cone F} (hc : is_terminal c)
  (s : cone F) : is_terminal.from hc s =
    ((cone.is_limit_equiv_is_terminal _).symm hc).lift_cone_morphism s :=
by convert (is_limit.lift_cone_morphism_eq_is_terminal_from _ s).symm

/-- If `G : cone F ⥤ cone F'` preserves terminal objects, it preserves limit cones. -/
def is_limit.of_preserves_cone_terminal {F : J ⥤ C} {F' : K ⥤ D} (G : cone F ⥤ cone F')
  [preserves_limit (functor.empty.{0} _) G] {c : cone F} (hc : is_limit c) :
  is_limit (G.obj c) :=
(cone.is_limit_equiv_is_terminal _).symm $
  (cone.is_limit_equiv_is_terminal _ hc).is_terminal_obj _ _

/-- If `G : cone F ⥤ cone F'` reflects terminal objects, it reflects limit cones. -/
def is_limit.of_reflects_cone_terminal {F : J ⥤ C} {F' : K ⥤ D} (G : cone F ⥤ cone F')
  [reflects_limit (functor.empty.{0} _) G] {c : cone F} (hc : is_limit (G.obj c)) :
  is_limit c :=
(cone.is_limit_equiv_is_terminal _).symm $
  (cone.is_limit_equiv_is_terminal _ hc).is_terminal_of_obj _ _

/-- Construct an object of the category `(F ↓ Δ)` from a cocone on `F`. This is part of an
    equivalence, see `cocone.equiv_structured_arrow`. -/
@[simps]
def cocone.to_structured_arrow (F : J ⥤ C) : cocone F ⥤ structured_arrow F (const J) :=
{ obj := λ c, structured_arrow.mk c.ι,
  map := λ c d f, structured_arrow.hom_mk f.hom $ by { ext, simp } }

/-- Construct a cocone on `F` from an object of the category `(F ↓ Δ)`. This is part of an
    equivalence, see `cocone.equiv_structured_arrow`. -/
@[simps]
def cocone.from_structured_arrow (F : J ⥤ C) : structured_arrow F (const J) ⥤ cocone F :=
{ obj := λ c, ⟨c.right, c.hom⟩,
  map := λ c d f,
  { hom := f.right,
    w' := λ j, by { convert (congr_fun (congr_arg nat_trans.app f.w) j).symm, dsimp, simp } } }

/-- The category of cocones on `F` is just the comma category `(F ↓ Δ)`, where `Δ` is the constant
    functor. -/
@[simps]
def cocone.equiv_structured_arrow (F : J ⥤ C) : cocone F ≌ structured_arrow F (const J) :=
equivalence.mk (cocone.to_structured_arrow F) (cocone.from_structured_arrow F)
  (nat_iso.of_components cocones.eta (by tidy))
  (nat_iso.of_components (λ c, (structured_arrow.eta _).symm) (by tidy))

/-- A cocone is a colimit cocone iff it is initial. -/
def cocone.is_colimit_equiv_is_initial {F : J ⥤ C} (c : cocone F) : is_colimit c ≃ is_initial c :=
is_colimit.iso_unique_cocone_morphism.to_equiv.trans
{ to_fun := λ h, by exactI is_initial.of_unique _,
  inv_fun := λ h s, ⟨⟨is_initial.to h s⟩, λ a, is_initial.hom_ext h a _⟩,
  left_inv := by tidy,
  right_inv := by tidy }

lemma has_colimit_iff_has_initial_cocone (F : J ⥤ C) : has_colimit F ↔ has_initial (cocone F) :=
⟨λ h, by exactI (cocone.is_colimit_equiv_is_initial _ (colimit.is_colimit F)).has_initial,
 λ h, ⟨⟨by exactI ⟨⊥_ _, (cocone.is_colimit_equiv_is_initial _).symm initial_is_initial⟩⟩⟩⟩

lemma has_colimits_of_shape_iff_is_right_adjoint_const :
  has_colimits_of_shape J C ↔ nonempty (is_right_adjoint (const J : C ⥤ _)) :=
calc has_colimits_of_shape J C
      ↔ ∀ F : J ⥤ C, has_colimit F : ⟨λ h, h.has_colimit, λ h, by exactI has_colimits_of_shape.mk⟩
  ... ↔ ∀ F : J ⥤ C, has_initial (cocone F) : forall_congr has_colimit_iff_has_initial_cocone
  ... ↔ ∀ F : J ⥤ C, has_initial (structured_arrow F (const J)) :
    forall_congr $ λ F, (cocone.equiv_structured_arrow F).has_initial_iff
  ... ↔ nonempty (is_right_adjoint (const J : C ⥤ _)) :
    nonempty_is_right_adjoint_iff_has_initial_structured_arrow.symm

lemma is_colimit.desc_cocone_morphism_eq_is_initial_to {F : J ⥤ C} {c : cocone F}
  (hc : is_colimit c) (s : cocone F) :
  hc.desc_cocone_morphism s =
    is_initial.to (cocone.is_colimit_equiv_is_initial _ hc) _ := rfl

lemma is_initial.to_eq_desc_cocone_morphism {F : J ⥤ C} {c : cocone F}
  (hc : is_initial c) (s : cocone F) :
  is_initial.to hc s = ((cocone.is_colimit_equiv_is_initial _).symm hc).desc_cocone_morphism s :=
by convert (is_colimit.desc_cocone_morphism_eq_is_initial_to _ s).symm

/-- If `G : cocone F ⥤ cocone F'` preserves initial objects, it preserves colimit cocones. -/
def is_colimit.of_preserves_cocone_initial {F : J ⥤ C} {F' : K ⥤ D} (G : cocone F ⥤ cocone F')
  [preserves_colimit (functor.empty.{0} _) G] {c : cocone F} (hc : is_colimit c) :
  is_colimit (G.obj c) :=
(cocone.is_colimit_equiv_is_initial _).symm $
  (cocone.is_colimit_equiv_is_initial _ hc).is_initial_obj _ _

/-- If `G : cocone F ⥤ cocone F'` reflects initial objects, it reflects colimit cocones. -/
def is_colimit.of_reflects_cocone_initial {F : J ⥤ C} {F' : K ⥤ D} (G : cocone F ⥤ cocone F')
  [reflects_colimit (functor.empty.{0} _) G] {c : cocone F} (hc : is_colimit (G.obj c)) :
  is_colimit c :=
(cocone.is_colimit_equiv_is_initial _).symm $
  (cocone.is_colimit_equiv_is_initial _ hc).is_initial_of_obj _ _

end category_theory.limits

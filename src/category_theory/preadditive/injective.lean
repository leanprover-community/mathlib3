/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/

import algebra.homology.exact
import category_theory.types
import category_theory.preadditive.projective
import category_theory.limits.shapes.biproducts

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/--
An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/
class injective (J : C) : Prop :=
(factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [mono f], ∃ h : Y ⟶ J, f ≫ h = g)

section
/--
An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
@[nolint has_inhabited_instance]
structure injective_presentation (X : C) :=
(J : C)
(injective : injective J . tactic.apply_instance)
(f : X ⟶ J)
(mono : mono f . tactic.apply_instance)

variables (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
class enough_injectives : Prop :=
(presentation : ∀ (X : C), nonempty (injective_presentation X))

end

namespace injective

/--
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factor_thru {J X Y : C} [injective J] (g : X ⟶ J) (f : X ⟶ Y) [mono f] : Y ⟶ J :=
(injective.factors g f).some

@[simp] lemma comp_factor_thru {J X Y : C} [injective J] (g : X ⟶ J) (f : X ⟶ Y) [mono f] :
  f ≫ factor_thru g f = g :=
(injective.factors g f).some_spec

section
open_locale zero_object

instance zero_injective [has_zero_object C] [has_zero_morphisms C] : injective (0 : C) :=
{ factors := λ X Y g f mono, ⟨0, by ext⟩ }

end

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : injective P) : injective Q :=
{ factors := λ X Y g f mono, begin
  obtain ⟨h, h_eq⟩ := @injective.factors C _ P _ _ _ (g ≫ i.inv) f mono,
  refine ⟨h ≫ i.hom, _⟩,
  rw [←category.assoc, h_eq, category.assoc, iso.inv_hom_id, category.comp_id],
end }

lemma iso_iff {P Q : C} (i : P ≅ Q) : injective P ↔ injective Q :=
⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u) [nonempty X] : injective X :=
{ factors := λ Y Z g f mono,
  ⟨λ z, by classical; exact
    if h : z ∈ set.range f
    then g (classical.some h)
    else nonempty.some infer_instance, begin
    ext y,
    change dite _ _ _ = _,
    split_ifs,
    { rw mono_iff_injective at mono,
      rw mono (classical.some_spec h) },
    { exact false.elim (h ⟨y, rfl⟩) },
  end⟩ }

instance Type.enough_injectives : enough_injectives (Type u) :=
{ presentation := λ X, nonempty.intro
  { J := with_bot X,
    injective := infer_instance,
    f := option.some,
    mono := by { rw [mono_iff_injective], exact option.some_injective X, } } }

instance {P Q : C} [has_binary_product P Q] [injective P] [injective Q] :
  injective (P ⨯ Q) :=
{ factors := λ X Y g f mono, begin
  resetI,
  use limits.prod.lift (factor_thru (g ≫ limits.prod.fst) f) (factor_thru (g ≫ limits.prod.snd) f),
  simp only [prod.comp_lift, comp_factor_thru],
  ext,
  { simp only [prod.lift_fst] },
  { simp only [prod.lift_snd] },
end }

instance {β : Type v} (c : β → C) [has_product c] [∀ b, injective (c b)] :
  injective (∏ c) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨pi.lift (λ b, factor_thru (g ≫ (pi.π c _)) f), _⟩,
  ext,
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, comp_factor_thru],
end }

instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q]
  [injective P] [injective Q] :
  injective (P ⊞ Q) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨biprod.lift (factor_thru (g ≫ biprod.fst) f) (factor_thru (g ≫ biprod.snd) f), _⟩,
  ext,
  { simp only [category.assoc, biprod.lift_fst, comp_factor_thru] },
  { simp only [category.assoc, biprod.lift_snd, comp_factor_thru] },
end }

instance {β : Type v} [decidable_eq β] (c : β → C) [has_zero_morphisms C] [has_biproduct c]
  [∀ b, injective (c b)] : injective (⨁ c) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨biproduct.lift (λ b, factor_thru (g ≫ biproduct.π _ _) f), _⟩,
  ext,
  simp only [category.assoc, biproduct.lift_π, comp_factor_thru],
end }

instance {P : Cᵒᵖ} [projective P] : injective (P.unop) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨(@projective.factor_thru Cᵒᵖ _ P (opposite.op X) (opposite.op Y) _ g.op f.op _).unop, _⟩,
  convert congr_arg quiver.hom.unop (@projective.factor_thru_comp Cᵒᵖ _ P
    (opposite.op X) (opposite.op Y) _ g.op f.op _),
end }

instance {J : C} [injective J] : projective (opposite.op J) :=
{ factors := λ E X f e epi, begin
  resetI,
  refine ⟨(@factor_thru C _ J _ _ _ f.unop e.unop _).op, _⟩,
  convert congr_arg quiver.hom.op (@comp_factor_thru C _ J _ _ _ f.unop e.unop _),
end }

end injective

end category_theory

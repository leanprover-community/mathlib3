/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import algebra.homology.exact
import category_theory.types
import category_theory.preadditive.projective
import category_theory.limits.shapes.biproducts

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/--
An object `J` is said to be injetive iff every morphism into `I` can be obtained by extending
monomorphism.-/
class injective (J : C) : Prop :=
(factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [mono f], ∃ h : Y ⟶ J, f ≫ h = g)

section
/--
An injective presentation of an object `X` consists of an monomorphism `f : X ⟶ J`
from some injective object `J`.
-/
@[nolint has_inhabited_instance]
structure injective_presentation (X : C) :=
(J : C)
(injective : injective J . tactic.apply_instance)
(f : X ⟶ J)
(mono : mono f . tactic.apply_instance)

variables (C)

/-- A category "has enough injectives" if for every object `X` there is an injective object `J` and
    a monomorphism `X ↪ J`. -/
class enough_injectives : Prop :=
(presentation : ∀ (X : C), nonempty (injective_presentation X))

end

namespace injective

/--
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factor_of {J X Y : C} [injective J] (g : X ⟶ J) (f : X ⟶ Y) [mono f] : Y ⟶ J :=
(injective.factors g f).some

@[simp] lemma factor_of_comp {J X Y : C} [injective J] (g : X ⟶ J) (f : X ⟶ Y) [mono f] :
  f ≫ factor_of g f = g :=
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

set_option pp.proofs true
/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u) [nonempty X] : injective X :=
{ factors := λ Y Z g f mono, ⟨λ z, by classical; exact if h : z ∈ set.range f then g (classical.some h) else
  nonempty.some infer_instance, begin
    ext y,
    change dite _ _ _ = _,
    split_ifs,
    { rw mono_iff_injective at mono,
      rw mono (classical.some_spec h) },
    { exact false.elim (h ⟨y, rfl⟩) },
  end⟩ }

instance Type.enough_injectives : enough_injectives (Type u) :=
{ presentation := λ X, ⟨{ J := with_bot X,
  injective := by apply_instance,
  f := option.some,
  mono := begin rw [mono_iff_injective], exact option.some_injective X, end }⟩, }

instance {P Q : C} [has_binary_product P Q] [injective P] [injective Q] :
  injective (P ⨯ Q) :=
{ factors := λ X Y g f mono, begin
  resetI,
  use limits.prod.lift (factor_of (g ≫ limits.prod.fst) f) (factor_of (g ≫ limits.prod.snd) f),
  simp only [prod.comp_lift, factor_of_comp],
  ext,
  { simp only [prod.lift_fst] },
  { simp only [prod.lift_snd] },
end }

instance {β : Type v} (c : β → C) [has_product c] [∀ b, injective (c b)] :
  injective (∏ c) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨pi.lift (λ b, factor_of (g ≫ (pi.π c _)) f), _⟩,
  ext,
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, factor_of_comp],
end }

-- disjoint unions should be injective?
instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q]
  [injective P] [injective Q] :
  injective (P ⊞ Q) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨biprod.lift (factor_of (g ≫ biprod.fst) f) (factor_of (g ≫ biprod.snd) f), _⟩,
  ext,
  simp only [category.assoc, biprod.lift_fst, factor_of_comp],
  simp only [category.assoc, biprod.lift_snd, factor_of_comp],
end }

instance {β : Type v} [decidable_eq β] (c : β → C) [has_zero_morphisms C] [has_biproduct c]
  [∀ b, injective (c b)] : injective (⨁ c) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨biproduct.lift (λ b, factor_of (g ≫ biproduct.π _ _) f), _⟩,
  ext,
  simp only [category.assoc, biproduct.lift_π, factor_of_comp],
end }

instance {P : Cᵒᵖ} [projective P] : injective (P.unop) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨(@projective.factor_thru Cᵒᵖ _ P (opposite.op X) (opposite.op Y) _ g.op f.op _).unop, _⟩,
  have eq1 := congr_arg quiver.hom.unop (@projective.factor_thru_comp Cᵒᵖ _ P (opposite.op X) (opposite.op Y) _ g.op f.op _),
  rw [quiver.hom.unop_op] at eq1,
  exact eq1,
end }

instance {J : C} [injective J] : projective (opposite.op J) :=
{ factors := λ E X f e epi, begin
  resetI,
  refine ⟨(@factor_of C _ J _ _ _ f.unop e.unop _).op, _⟩,
  have eq1 := congr_arg quiver.hom.op (@factor_of_comp C _ J _ _ _ f.unop e.unop _),
  rw [quiver.hom.op_unop] at eq1,
  exact eq1,
end }

-- STOP HERE AND PR

section enough_injectives
variable [enough_injectives C]

/--
`injective.under X` provides an arbitrarily chosen injective object equipped with
an monomorphism `projective.ι : X ⟶ injective.under X`.
-/
def under (X : C) : C :=
(enough_injectives.presentation X).some.J

instance injective_under (X : C) : injective (under X) :=
(enough_injectives.presentation X).some.injective

/--
The monomorphism `injective.ι : X ⟶ injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
(enough_injectives.presentation X).some.f

instance ι_mono (X : C) : mono (ι X) :=
(enough_injectives.presentation X).some.mono

section
variables [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_cokernel f]

/--
When `C` has enough injectives, the object `injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
@[derive injective]
def syzygies : C := under (cokernel f)

/--
When `C` has enough injective,
`injective.d f : Y ⟶ syzygies f` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbreviation d : Y ⟶ syzygies f :=
cokernel.π f ≫ ι (cokernel f)

end

end enough_injectives

open injective

section
variables [has_zero_morphisms C] [has_images Cᵒᵖ] [has_equalizers Cᵒᵖ]

/--
Given a projective object `P` mapping via `h` into
the middle object `R` of a pair of exact morphisms `f : Q ⟶ R` and `g : R ⟶ S`,
such that `h ≫ g = 0`, there is a lift of `h` to `Q`.
-/
def exact.desc {J Q R S : C} [injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S) [exact g.op f.op]
  (w : f ≫ h = 0)  : S ⟶ J :=
(exact.lift h.op g.op f.op (congr_arg quiver.hom.op w)).unop

@[simp] lemma exact.desc_comp {J Q R S : C} [injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S)
  [exact g.op f.op] (w : f ≫ h = 0) : g ≫ exact.desc h f g w = h :=
begin
  have := congr_arg quiver.hom.unop (exact.lift_comp h.op g.op f.op (congr_arg quiver.hom.op w)),
  simp only [quiver.hom.unop_op] at this,
  convert this,
end

end

end injective

end category_theory

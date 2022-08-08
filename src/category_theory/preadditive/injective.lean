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
open opposite

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
@[nolint has_nonempty_instance]
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
  ext ⟨j⟩,
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

instance {β : Type v} (c : β → C) [has_zero_morphisms C] [has_biproduct c]
  [∀ b, injective (c b)] : injective (⨁ c) :=
{ factors := λ X Y g f mono, begin
  resetI,
  refine ⟨biproduct.lift (λ b, factor_thru (g ≫ biproduct.π _ _) f), _⟩,
  ext,
  simp only [category.assoc, biproduct.lift_π, comp_factor_thru],
end }

instance {P : Cᵒᵖ} [projective P] : injective (unop P) :=
{ factors := λ X Y g f mono, by exactI ⟨(@projective.factor_thru Cᵒᵖ _ P _ _ _ g.op f.op _).unop,
      quiver.hom.op_inj (by simp)⟩ }

instance {J : Cᵒᵖ} [injective J] : projective (unop J) :=
{ factors := λ E X f e he, by exactI ⟨(@factor_thru Cᵒᵖ _ J _ _ _ f.op e.op _).unop,
    quiver.hom.op_inj (by simp)⟩ }

instance {J : C} [injective J] : projective (op J) :=
{ factors := λ E X f e epi, by exactI ⟨(@factor_thru C _ J _ _ _ f.unop e.unop _).op,
    quiver.hom.unop_inj (by simp)⟩ }

instance {P : C} [projective P] : injective (op P) :=
{ factors := λ X Y g f mono, by exactI ⟨(@projective.factor_thru C _ P _ _ _ g.unop f.unop _).op,
    quiver.hom.unop_inj (by simp)⟩ }

lemma injective_iff_projective_op {J : C} : injective J ↔ projective (op J) :=
⟨λ h, by exactI infer_instance, λ h, show injective (unop (op J)), by exactI infer_instance⟩

lemma projective_iff_injective_op {P : C} : projective P ↔ injective (op P) :=
⟨λ h, by exactI infer_instance, λ h, show projective (unop (op P)), by exactI infer_instance⟩

lemma injective_iff_preserves_epimorphisms_yoneda_obj (J : C) :
  injective J ↔ (yoneda.obj J).preserves_epimorphisms :=
begin
  rw [injective_iff_projective_op, projective.projective_iff_preserves_epimorphisms_coyoneda_obj],
  exact functor.preserves_epimorphisms.iso_iff (coyoneda.obj_op_op _)
end

section adjunction

 open category_theory.functor

 universes v₁ v₂ u₁ u₂

 variables {𝓐 : Type u₁} {𝓑 : Type u₂} [category.{v₁ u₁} 𝓐] [category.{v₂ u₂} 𝓑]
 variables {L : 𝓐 ⥤ 𝓑} {R : 𝓑 ⥤ 𝓐} (adj : L ⊣ R) [preserves_monomorphisms L]

 include adj
 def injective_of_adjoint {J : 𝓑} [injective J] : injective $ R.obj J :=
 { factors := λ A A' g f im,
   begin
     resetI,
     haveI : mono (L.map f) := functor.map_mono L _,
     refine ⟨adj.hom_equiv _ _ (factor_thru ((adj.hom_equiv A J).symm g) (L.map f)), _⟩,
     apply_fun (adj.hom_equiv _ _).symm using equiv.injective,
     simp,
   end }

 end adjunction

section enough_injectives
variable [enough_injectives C]

/--
`injective.under X` provides an arbitrarily chosen injective object equipped with
an monomorphism `injective.ι : X ⟶ injective.under X`.
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
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbreviation d : Y ⟶ syzygies f :=
cokernel.π f ≫ ι (cokernel f)

end

end enough_injectives

instance [enough_injectives C] : enough_projectives Cᵒᵖ :=
⟨λ X, ⟨⟨_, infer_instance, (injective.ι (unop X)).op, infer_instance⟩⟩⟩

instance [enough_projectives C] : enough_injectives Cᵒᵖ :=
⟨λ X, ⟨⟨_, infer_instance, (projective.π (unop X)).op, infer_instance⟩⟩⟩

lemma enough_projectives_of_enough_injectives_op [enough_injectives Cᵒᵖ] : enough_projectives C :=
⟨λ X, ⟨⟨_, infer_instance, (injective.ι (op X)).unop, infer_instance⟩⟩⟩

lemma enough_injectives_of_enough_projectives_op [enough_projectives Cᵒᵖ] : enough_injectives C :=
⟨λ X, ⟨⟨_, infer_instance, (projective.π (op X)).unop, infer_instance⟩⟩⟩

open injective

section
variables [has_zero_morphisms C] [has_images Cᵒᵖ] [has_equalizers Cᵒᵖ]

/--
Given a pair of exact morphism `f : Q ⟶ R` and `g : R ⟶ S` and a map `h : R ⟶ J` to an injective
object `J` such that `f ≫ h = 0`, then `g` descents to a map `S ⟶ J`. See below:

```
Q --- f --> R --- g --> S
            |
            | h
            v
            J
```
-/
def exact.desc {J Q R S : C} [injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S)
  (hgf : exact g.op f.op) (w : f ≫ h = 0)  : S ⟶ J :=
(exact.lift h.op g.op f.op hgf (congr_arg quiver.hom.op w)).unop

@[simp] lemma exact.comp_desc {J Q R S : C} [injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S)
  (hgf : exact g.op f.op) (w : f ≫ h = 0) : g ≫ exact.desc h f g hgf w = h :=
by convert congr_arg quiver.hom.unop
  (exact.lift_comp h.op g.op f.op hgf (congr_arg quiver.hom.op w))

end

end injective

end category_theory

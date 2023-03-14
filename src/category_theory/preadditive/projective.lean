/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import algebra.homology.exact
import category_theory.types
import category_theory.limits.shapes.biproducts
import category_theory.adjunction.limits
import category_theory.preadditive.yoneda.basic
import algebra.category.Group.epi_mono
import algebra.category.Module.epi_mono

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
-/

noncomputable theory

open category_theory
open category_theory.limits
open opposite

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/--
An object `P` is called projective if every morphism out of `P` factors through every epimorphism.
-/
class projective (P : C) : Prop :=
(factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [epi e], ∃ f', f' ≫ e = f)

section

/--
A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
@[nolint has_nonempty_instance]
structure projective_presentation (X : C) :=
(P : C)
(projective : projective P . tactic.apply_instance)
(f : P ⟶ X)
(epi : epi f . tactic.apply_instance)

attribute [instance] projective_presentation.projective projective_presentation.epi

variables (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives : Prop :=
(presentation : ∀ (X : C), nonempty (projective_presentation X))

end

namespace projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factor_thru {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] : P ⟶ E :=
(projective.factors f e).some

@[simp] lemma factor_thru_comp {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] :
  factor_thru f e ≫ e = f :=
(projective.factors f e).some_spec

section
open_locale zero_object

instance zero_projective [has_zero_object C] [has_zero_morphisms C] : projective (0 : C) :=
{ factors := λ E X f e epi, by { use 0, ext, }}

end

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
begin
  fsplit,
  introsI E X f e e_epi,
  obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e,
  exact ⟨i.inv ≫ f', by simp [hf']⟩
end

lemma iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : projective X :=
{ factors := λ E X' f e epi,
  ⟨λ x, ((epi_iff_surjective _).mp epi (f x)).some,
  by { ext x, exact ((epi_iff_surjective _).mp epi (f x)).some_spec, }⟩ }

instance Type.enough_projectives : enough_projectives (Type u) :=
{ presentation := λ X, ⟨{ P := X, f := 𝟙 X, }⟩, }

instance {P Q : C} [has_binary_coproduct P Q] [projective P] [projective Q] :
  projective (P ⨿ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨coprod.desc (factor_thru (coprod.inl ≫ f) e) (factor_thru (coprod.inr ≫ f) e), by tidy⟩, }

section
local attribute [tidy] tactic.discrete_cases

instance {β : Type v} (g : β → C) [has_coproduct g] [∀ b, projective (g b)] :
  projective (∐ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨sigma.desc (λ b, factor_thru (sigma.ι g b ≫ f) e), by tidy⟩, }

end

instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q]
  [projective P] [projective Q] :
  projective (P ⊞ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biprod.desc (factor_thru (biprod.inl ≫ f) e) (factor_thru (biprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} (g : β → C) [has_zero_morphisms C] [has_biproduct g]
  [∀ b, projective (g b)] : projective (⨁ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biproduct.desc (λ b, factor_thru (biproduct.ι g b ≫ f) e), by tidy⟩, }

lemma projective_iff_preserves_epimorphisms_coyoneda_obj (P : C) :
  projective P ↔ (coyoneda.obj (op P)).preserves_epimorphisms :=
⟨λ hP, ⟨λ X Y f hf, (epi_iff_surjective _).2 $ λ g, have projective (unop (op P)), from hP,
  by exactI ⟨factor_thru g f, factor_thru_comp _ _⟩⟩,
 λ h, ⟨λ E X f e he, by exactI (epi_iff_surjective _).1
  (infer_instance : epi ((coyoneda.obj (op P)).map e)) f⟩⟩

section preadditive
variables [preadditive C]

lemma projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj (P : C) :
  projective P ↔ (preadditive_coyoneda.obj (op P)).preserves_epimorphisms :=
begin
  rw projective_iff_preserves_epimorphisms_coyoneda_obj,
  refine ⟨λ (h : (preadditive_coyoneda.obj (op P) ⋙ (forget _)).preserves_epimorphisms), _, _⟩,
  { exactI functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda.obj (op P))
      (forget _) },
  { introI,
    exact (infer_instance : (preadditive_coyoneda.obj (op P) ⋙ forget _).preserves_epimorphisms) }
end

lemma projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' (P : C) :
  projective P ↔ (preadditive_coyoneda_obj (op P)).preserves_epimorphisms :=
begin
  rw projective_iff_preserves_epimorphisms_coyoneda_obj,
  refine ⟨λ (h : (preadditive_coyoneda_obj (op P) ⋙ (forget _)).preserves_epimorphisms), _, _⟩,
  { exactI functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda_obj (op P))
      (forget _) },
  { introI,
    exact (infer_instance : (preadditive_coyoneda_obj (op P) ⋙ forget _).preserves_epimorphisms) }
end

end preadditive

section enough_projectives
variables [enough_projectives C]

/--
`projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `projective.π : projective.over X ⟶ X`.
-/
def over (X : C) : C :=
(enough_projectives.presentation X).some.P

instance projective_over (X : C) : projective (over X) :=
(enough_projectives.presentation X).some.projective

/--
The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
(enough_projectives.presentation X).some.f

instance π_epi (X : C) : epi (π X) :=
(enough_projectives.presentation X).some.epi

section
variables [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_kernel f]

/--
When `C` has enough projectives, the object `projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
@[derive projective]
def syzygies : C := over (kernel f)

/--
When `C` has enough projectives,
`projective.d f : projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
abbreviation d : syzygies f ⟶ X :=
π (kernel f) ≫ kernel.ι f

end

end enough_projectives

end projective
namespace adjunction

variables {D : Type*} [category D] {F : C ⥤ D} {G : D ⥤ C}

lemma map_projective (adj : F ⊣ G) [G.preserves_epimorphisms] (P : C) (hP : projective P) :
  projective (F.obj P) :=
⟨λ X Y f g, begin
  introI,
  rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g),
  use F.map w ≫ adj.counit.app X,
  rw [category.assoc, ←adjunction.counit_naturality, ←category.assoc, ←F.map_comp, h],
  simp,
end⟩

lemma projective_of_map_projective (adj : F ⊣ G) [full F] [faithful F] (P : C)
  (hP : projective (F.obj P)) : projective P :=
⟨λ X Y f g, begin
  introI,
  haveI := adj.left_adjoint_preserves_colimits,
  rcases @hP.1 (F.map f) (F.map g),
  use adj.unit.app _ ≫ G.map w ≫ (inv $ adj.unit.app _),
  refine faithful.map_injective F _,
  simpa
end⟩

/-- Given an adjunction `F ⊣ G` such that `G` preserves epis, `F` maps a projective presentation of
`X` to a projective presentation of `F(X)`. -/
def map_projective_presentation (adj : F ⊣ G) [G.preserves_epimorphisms] (X : C)
  (Y : projective_presentation X) : projective_presentation (F.obj X) :=
{ P := F.obj Y.P,
  projective := adj.map_projective _ Y.projective,
  f := F.map Y.f,
  epi := by haveI := adj.left_adjoint_preserves_colimits; apply_instance }

end adjunction
namespace equivalence

variables {D : Type*} [category D] (F : C ≌ D)

/-- Given an equivalence of categories `F`, a projective presentation of `F(X)` induces a
projective presentation of `X.` -/
def projective_presentation_of_map_projective_presentation
  (X : C) (Y : projective_presentation (F.functor.obj X)) : projective_presentation X :=
{ P := F.inverse.obj Y.P,
  projective := adjunction.map_projective F.symm.to_adjunction Y.P Y.projective,
  f := F.inverse.map Y.f ≫ F.unit_inv.app _,
  epi := epi_comp _ _ }

lemma enough_projectives_iff (F : C ≌ D) :
  enough_projectives C ↔ enough_projectives D :=
begin
  split,
  all_goals { intro H, constructor, intro X, constructor },
  { exact F.symm.projective_presentation_of_map_projective_presentation _
      (nonempty.some (H.presentation (F.inverse.obj X))) },
  { exact F.projective_presentation_of_map_projective_presentation X
      (nonempty.some (H.presentation (F.functor.obj X))) },
end

end equivalence
open projective
section
variables [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
Given a projective object `P` mapping via `h` into
the middle object `R` of a pair of exact morphisms `f : Q ⟶ R` and `g : R ⟶ S`,
such that `h ≫ g = 0`, there is a lift of `h` to `Q`.
-/
def exact.lift {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
  (hfg : exact f g) (w : h ≫ g = 0) : P ⟶ Q :=
factor_thru
  (factor_thru
    (factor_thru_kernel_subobject g h w)
    (image_to_kernel f g hfg.w))
  (factor_thru_image_subobject f)

@[simp] lemma exact.lift_comp {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
  (hfg : exact f g) (w : h ≫ g = 0) : exact.lift h f g hfg w ≫ f = h :=
begin
  simp [exact.lift],
  conv_lhs { congr, skip, rw ← image_subobject_arrow_comp f, },
  rw [←category.assoc, factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

end

end category_theory

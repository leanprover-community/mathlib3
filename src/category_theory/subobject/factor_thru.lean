/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.subobject.basic

/-!
# Factoring through subobjects

The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.
We provide conditions for `P.factors f`, when `P` is a kernel/equalizer/image/inf/sup subobject.

TODO: Add conditions for when `P` is a pullback subobject.

-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

namespace category_theory

namespace mono_over

/-- When `f : X ⟶ Y` and `P : mono_over Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : mono_over Y) (f : X ⟶ Y) : Prop := ∃ g : X ⟶ P.val.left, g ≫ P.arrow = f

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : mono_over Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : mono_over Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ P.val.left :=
classical.some h

end mono_over

namespace subobject

/-- When `f : X ⟶ Y` and `P : subobject Y`,
`P.factors f` expresses that there exists a factorisation of `f` through `P`.
Given `h : P.factors f`, you can recover the morphism as `P.factor_thru f h`.
-/
def factors {X Y : C} (P : subobject Y) (f : X ⟶ Y) : Prop :=
quotient.lift_on' P (λ P, P.factors f)
begin
  rintros P Q ⟨h⟩,
  apply propext,
  split,
  { rintro ⟨i, w⟩,
    exact ⟨i ≫ h.hom.left, by erw [category.assoc, over.w h.hom, w]⟩, },
  { rintro ⟨i, w⟩,
    exact ⟨i ≫ h.inv.left, by erw [category.assoc, over.w h.inv, w]⟩, },
end

lemma factors_iff {X Y : C} (P : subobject Y) (f : X ⟶ Y) :
  P.factors f ↔ (representative.obj P).factors f :=
begin
  induction P,
  { rcases P with ⟨⟨P, ⟨⟩, g⟩, hg⟩,
    resetI,
    fsplit,
    { rintro ⟨i, w⟩,
      refine ⟨i ≫ (underlying_iso g).inv, _⟩,
      simp only [category_theory.category.assoc],
      convert w,
      convert underlying_iso_arrow _, },
    { rintro ⟨i, w⟩,
      refine ⟨i ≫ (underlying_iso g).hom, _⟩,
      simp only [category_theory.category.assoc],
      convert w,
      rw ←iso.eq_inv_comp,
      symmetry,
      convert underlying_iso_arrow _, }, },
  { refl, },
end

/-- `P.factor_thru f h` provides a factorisation of `f : X ⟶ Y` through some `P : subobject Y`,
given the evidence `h : P.factors f` that such a factorisation exists. -/
def factor_thru {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) : X ⟶ P :=
classical.some ((factors_iff _ _).mp h)

@[simp, reassoc] lemma factor_thru_arrow {X Y : C} (P : subobject Y) (f : X ⟶ Y) (h : factors P f) :
  P.factor_thru f h ≫ P.arrow = f :=
classical.some_spec ((factors_iff _ _).mp h)

@[simp] lemma factor_thru_eq_zero [has_zero_morphisms C]
  {X Y : C} {P : subobject Y} {f : X ⟶ Y} {h : factors P f} :
  P.factor_thru f h = 0 ↔ f = 0 :=
begin
  fsplit,
  { intro w,
    replace w := w =≫ P.arrow,
    simpa using w, },
  { rintro rfl,
    apply (cancel_mono P.arrow).mp,
    simp, },
end

lemma factors_comp_arrow {X Y : C} {P : subobject Y} (f : X ⟶ P) : P.factors (f ≫ P.arrow) :=
(factors_iff _ _).mpr ⟨f, rfl⟩

lemma factors_of_factors_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
  (h : P.factors g) : P.factors (f ≫ g) :=
begin
  revert P,
  refine quotient.ind' _,
  intro P,
  rintro ⟨g, rfl⟩,
  exact ⟨f ≫ g, by simp⟩,
end

lemma factors_of_le {Y Z : C} {P Q : subobject Y} (f : Z ⟶ Y) (h : P ≤ Q) :
  P.factors f → Q.factors f :=
begin
  revert P Q,
  refine quotient.ind₂' _,
  rintro P Q ⟨h⟩ ⟨g, rfl⟩,
  refine ⟨g ≫ h.left, _⟩,
  rw assoc,
  congr' 1,
  apply over.w h,
end

@[simp]
lemma factor_thru_right {X Y Z : C} {P : subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.factors g) :
  f ≫ P.factor_thru g h = P.factor_thru (f ≫ g) (factors_of_factors_right f h) :=
begin
  apply (cancel_mono P.arrow).mp,
  simp,
end

end subobject

namespace limits

section equalizer
variables (f g : X ⟶ Y) [has_equalizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `subobject X`. -/
def equalizer_subobject : subobject X :=
subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizer_subobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizer_subobject_iso : (equalizer_subobject f g : C) ≅ equalizer f g :=
subobject.underlying_iso (equalizer.ι f g)

lemma equalizer_subobject_arrow :
  (equalizer_subobject f g).arrow = (equalizer_subobject_iso f g).hom ≫ equalizer.ι f g :=
(over.w (subobject.representative_iso (mono_over.mk' (equalizer.ι f g))).hom).symm

@[simp] lemma equalizer_subobject_arrow' :
  (equalizer_subobject_iso f g).inv ≫ (equalizer_subobject f g).arrow = equalizer.ι f g :=
over.w (subobject.representative_iso (mono_over.mk' (equalizer.ι f g))).inv

@[reassoc]
lemma equalizer_subobject_arrow_comp :
  (equalizer_subobject f g).arrow ≫ f = (equalizer_subobject f g).arrow ≫ g :=
by simp [equalizer_subobject_arrow, equalizer.condition]

lemma equalizer_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
  (equalizer_subobject f g).factors h :=
⟨equalizer.lift h w, by simp⟩

lemma equalizer_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (equalizer_subobject f g).factors h ↔ h ≫ f = h ≫ g :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  equalizer_subobject_arrow_comp, category.assoc],
equalizer_subobject_factors f g h⟩

end equalizer

section kernel
variables [has_zero_morphisms C] (f : X ⟶ Y) [has_kernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `subobject X`. -/
def kernel_subobject : subobject X :=
subobject.mk (kernel.ι f)

/-- The underlying object of `kernel_subobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernel_subobject_iso :
  (kernel_subobject f : C) ≅ kernel f :=
subobject.underlying_iso (kernel.ι f)

lemma kernel_subobject_arrow :
  (kernel_subobject f).arrow = (kernel_subobject_iso f).hom ≫ kernel.ι f :=
(over.w (subobject.representative_iso (mono_over.mk' (kernel.ι f))).hom).symm

@[simp] lemma kernel_subobject_arrow' :
  (kernel_subobject_iso f).inv ≫ (kernel_subobject f).arrow = kernel.ι f :=
over.w (subobject.representative_iso (mono_over.mk' (kernel.ι f))).inv

@[simp]
lemma kernel_subobject_arrow_comp :
  (kernel_subobject f).arrow ≫ f = 0 :=
by simp [kernel_subobject_arrow, kernel.condition]

lemma kernel_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
  (kernel_subobject f).factors h :=
⟨kernel.lift _ h w, by simp⟩

lemma kernel_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (kernel_subobject f).factors h ↔ h ≫ f = 0 :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  kernel_subobject_arrow_comp, comp_zero],
kernel_subobject_factors f h⟩

end kernel

section image
variables (f : X ⟶ Y) [has_image f]

/-- The image of a morphism `f g : X ⟶ Y` as a `subobject Y`. -/
def image_subobject : subobject Y :=
(to_thin_skeleton _).obj (mono_over.image_mono_over f)

/-- The underlying object of `image_subobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def image_subobject_iso :
  (image_subobject f : C) ≅ image f :=
subobject.underlying_iso (image.ι f)

lemma image_subobject_arrow :
  (image_subobject f).arrow = (image_subobject_iso f).hom ≫ image.ι f :=
(over.w (subobject.representative_iso (mono_over.mk' (image.ι f))).hom).symm

@[simp] lemma image_subobject_arrow' :
  (image_subobject_iso f).inv ≫ (image_subobject f).arrow = image.ι f :=
over.w (subobject.representative_iso (mono_over.mk' (image.ι f))).inv

/-- A factorisation of `f : X ⟶ Y` through `image_subobject f`. -/
def factor_thru_image_subobject : X ⟶ image_subobject f :=
factor_thru_image f ≫ (image_subobject_iso f).inv

lemma image_subobject_arrow_comp :
  factor_thru_image_subobject f ≫ (image_subobject f).arrow = f :=
by simp [factor_thru_image_subobject, image_subobject_arrow]

-- TODO an iff characterisation of `(image_subobject f).factors h`
lemma image_subobject_factors {W : C} (h : W ⟶ Y) (k : W ⟶ X) (w : k ≫ f = h) :
  (image_subobject f).factors h :=
⟨k ≫ factor_thru_image f, by simp [w]⟩

lemma image_subobject_le {A B : C} {X : subobject B} (f : A ⟶ B) [has_image f]
  (h : A ⟶ X) (w : h ≫ X.arrow = f) :
  image_subobject f ≤ X :=
subobject.le_of_comm
  ((image_subobject_iso f).hom ≫ image.lift { I := (X : C), e := h, m := X.arrow, })
  (by simp [←image_subobject_arrow f])

end image

end limits

end category_theory

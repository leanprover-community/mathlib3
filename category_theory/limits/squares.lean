-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section pullback
variables {Y₁ Y₂ Z : C} {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z}
structure is_pullback (t : square r₁ r₂) :=
(lift : ∀ (s : square r₁ r₂), s.X ⟶ t.X)
(fac₁' : ∀ (s : square r₁ r₂), (lift s ≫ t.π₁) = s.π₁ . obviously)
(fac₂' : ∀ (s : square r₁ r₂), (lift s ≫ t.π₂) = s.π₂ . obviously)
(uniq' : ∀ (s : square r₁ r₂) (m : s.X ⟶ t.X) (w₁ : (m ≫ t.π₁) = s.π₁) (w₂ : (m ≫ t.π₂) = s.π₂), m = lift s . obviously)

restate_axiom is_pullback.fac₁'
attribute [simp] is_pullback.fac₁
restate_axiom is_pullback.fac₂'
attribute [simp] is_pullback.fac₂
restate_axiom is_pullback.uniq'

@[extensionality] lemma is_pullback.ext {t : square r₁ r₂} (P Q : is_pullback t) : P = Q :=
begin
  cases P, cases Q,
  simp,
  ext1,
  exact eq.symm (P_uniq' x (Q_lift x) (Q_fac₁' x) (Q_fac₂' x))
end

lemma is_pullback.universal {t : square r₁ r₂} (h : is_pullback t) (s : square r₁ r₂) (φ : s.X ⟶ t.X) :
  (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
⟨ λ a, is_pullback.uniq h s φ a.1 a.2,
  λ a, ⟨ by rw [a, is_pullback.fac₁],
         by rw [a, is_pullback.fac₂] ⟩ ⟩

def is_pullback.of_lift_universal {t : square r₁ r₂}
  (lift : Π (s : square r₁ r₂), s.X ⟶ t.X)
  (universal : Π (s : square r₁ r₂) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) :
  is_pullback t :=
{ lift := lift,
  fac₁' := λ s, ((universal s (lift s)).mpr (eq.refl (lift s))).left,
  fac₂' := λ s, ((universal s (lift s)).mpr (eq.refl (lift s))).right,
  uniq' := λ s m w₁ w₂, (universal s m).mp ⟨w₁, w₂⟩ }

end pullback


section pushout
variables {Y₁ Y₂ Z : C} {r₁ : Z ⟶ Y₁} {r₂ : Z ⟶ Y₂}
structure is_pushout (t : cosquare r₁ r₂) :=
(desc : ∀ (s : cosquare r₁ r₂), t.X ⟶ s.X)
(fac₁' : ∀ (s : cosquare r₁ r₂), (t.ι₁ ≫ desc s) = s.ι₁ . obviously)
(fac₂' : ∀ (s : cosquare r₁ r₂), (t.ι₂ ≫ desc s) = s.ι₂ . obviously)
(uniq' : ∀ (s : cosquare r₁ r₂) (m : t.X ⟶ s.X) (w₁ : (t.ι₁ ≫ m) = s.ι₁) (w₂ : (t.ι₂ ≫ m) = s.ι₂), m = desc s . obviously)

restate_axiom is_pushout.fac₁'
attribute [simp] is_pushout.fac₁
restate_axiom is_pushout.fac₂'
attribute [simp] is_pushout.fac₂
restate_axiom is_pushout.uniq'

@[extensionality] lemma is_pushout.ext {t : cosquare r₁ r₂} (P Q : is_pushout t) : P = Q :=
begin
  cases P, cases Q,
  simp,
  ext1,
  exact eq.symm (P_uniq' x (Q_desc x) (Q_fac₁' x) (Q_fac₂' x))
end

lemma is_pushout.universal {t : cosquare r₁ r₂} (h : is_pushout t) (s : cosquare r₁ r₂) (φ : t.X ⟶ s.X) :
  (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = h.desc s) :=
⟨ λ a, is_pushout.uniq h s φ a.1 a.2,
  λ a, ⟨ by rw [a, is_pushout.fac₁],
         by rw [a, is_pushout.fac₂] ⟩ ⟩

def is_pushout.of_desc_universal {t : cosquare r₁ r₂}
  (desc : Π (s : cosquare r₁ r₂), t.X ⟶ s.X)
  (universal : Π (s : cosquare r₁ r₂) (φ : t.X ⟶ s.X), (t.ι₁ ≫ φ = s.ι₁ ∧ t.ι₂ ≫ φ = s.ι₂) ↔ (φ = desc s)) : is_pushout t :=
{ desc := desc,
  fac₁' := λ s, ((universal s (desc s)).mpr (eq.refl (desc s))).left,
  fac₂' := λ s, ((universal s (desc s)).mpr (eq.refl (desc s))).right,
  uniq' := λ s m w₁ w₂, (universal s m).mp ⟨w₁, w₂⟩ }

end pushout

variable (C)

class has_pullbacks :=
(square : Π {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z), square r₁ r₂)
(is_pullback : Π {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z), is_pullback (square r₁ r₂) . obviously)

class has_pushouts :=
(cosquare : Π {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂), cosquare r₁ r₂)
(is_pushout : Π {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂), is_pushout (cosquare r₁ r₂) . obviously)

variable {C}


section
variables [has_pullbacks.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z)

def pullback.square := has_pullbacks.square.{u v} r₁ r₂
def pullback := (pullback.square r₁ r₂).X
def pullback.π₁ : pullback r₁ r₂ ⟶ Y₁ := (pullback.square r₁ r₂).π₁
def pullback.π₂ : pullback r₁ r₂ ⟶ Y₂ := (pullback.square r₁ r₂).π₂
def pullback.universal_property : is_pullback (pullback.square r₁ r₂) := has_pullbacks.is_pullback.{u v} C r₁ r₂

@[extensionality] lemma pullback.hom_ext
  {X : C} (f g : X ⟶ pullback r₁ r₂)
  (w₁ : f ≫ pullback.π₁ r₁ r₂ = g ≫ pullback.π₁ r₁ r₂)
  (w₂ : f ≫ pullback.π₂ r₁ r₂ = g ≫ pullback.π₂ r₁ r₂) : f = g :=
begin
  let s : square r₁ r₂ :=
  { X := X,
    π₁ := f ≫ pullback.π₁ r₁ r₂,
    π₂ := f ≫ pullback.π₂ r₁ r₂,
    w' :=
    begin
      /- `obviously` says -/
      dsimp at *, simp at *,
      erw limits.square.w,
      refl,
    end
  },
  have q := (pullback.universal_property r₁ r₂).uniq s f,
  have p := (pullback.universal_property r₁ r₂).uniq s g,
  rw [q, ←p],
  exact eq.symm w₁,
  exact eq.symm w₂,
  refl,
  refl
end

end

section
variables [has_pushouts.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂)

def pushout.cosquare := has_pushouts.cosquare.{u v} r₁ r₂
def pushout := (pushout.cosquare r₁ r₂).X
def pushout.ι₁ : Y₁ ⟶ pushout r₁ r₂ := (pushout.cosquare r₁ r₂).ι₁
def pushout.ι₂ : Y₂ ⟶ pushout r₁ r₂ := (pushout.cosquare r₁ r₂).ι₂
def pushout.universal_property : is_pushout (pushout.cosquare r₁ r₂) := has_pushouts.is_pushout.{u v} C r₁ r₂

@[extensionality] lemma pushout.hom_ext
  {X : C} (f g : pushout r₁ r₂ ⟶ X)
  (w₁ : pushout.ι₁ r₁ r₂ ≫ f = pushout.ι₁ r₁ r₂ ≫ g)
  (w₂ : pushout.ι₂ r₁ r₂ ≫ f = pushout.ι₂ r₁ r₂ ≫ g) : f = g :=
begin
  let s : cosquare r₁ r₂ :=
  { X := X,
    ι₁ := pushout.ι₁ r₁ r₂ ≫ f,
    ι₂ := pushout.ι₂ r₁ r₂ ≫ f,
    w' :=
    begin
      /- `obviously` says -/
      rw ←category.assoc,
      erw limits.cosquare.w,
      rw ←category.assoc,
      refl,
    end },
  have q := (pushout.universal_property r₁ r₂).uniq s f,
  have p := (pushout.universal_property r₁ r₂).uniq s g,
  rw [q, ←p],
  exact eq.symm w₁,
  exact eq.symm w₂,
  refl,
  refl
end

end

end category_theory.limits

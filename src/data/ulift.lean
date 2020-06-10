/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Transport through constant families.
-/

universes u₁ u₂

@[simp] lemma plift.rec.constant {α : Sort u₁} {β : Sort u₂} (b : β) :
  @plift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, plift.cases_on x (λ a, eq.refl (plift.rec (λ a', b) {down := a})))

@[simp] lemma ulift.rec.constant {α : Type u₁} {β : Sort u₂} (b : β) :
  @ulift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, ulift.cases_on x (λ a, eq.refl (ulift.rec (λ a', b) {down := a})))

-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import category_theory.isomorphism

namespace category_theory

universes u₁ v₁ u₂ v₂

def discrete (α : Type u₁) := α

-- TODO find a home for these in mathlib. https://leanprover.zulipchat.com/#narrow/stream/113488-general/subject/transport.20through.20trivial.20bundles/near/125769004
@[simp] lemma plift.rec.constant {α : Sort u₁} {β : Sort u₂} (b : β) : @plift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, plift.cases_on x (λ a, eq.refl (plift.rec (λ a', b) {down := a})))

@[simp] lemma ulift.rec.constant {α : Type u₁} {β : Sort u₂} (b : β) : @ulift.rec α (λ _, β) (λ _, b) = λ _, b :=
funext (λ x, ulift.cases_on x (λ a, eq.refl (ulift.rec (λ a', b) {down := a})))

@[extensionality] lemma plift.ext {P : Prop} (a b : plift P) : a = b :=
begin
  cases a, cases b, refl
end

instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X = Y)),
  id   := by obviously,
  comp := by obviously }

instance pempty_category : small_category pempty := (by apply_instance : small_category (discrete pempty))

instance punit_category : category.{u₁ v₁} punit :=
{ hom  := λ X Y, punit,
  id   := by obviously,
  comp := by obviously }

-- TODO this needs to wait for equivalences to arrive
-- example : equivalence.{u₁ u₁ u₁ u₁} punit (discrete punit) := by obviously

namespace functor
variables (C : Type u₂) [𝒞 : category.{u₂ v₂} C]
include 𝒞

def empty : pempty ⥤ C := by obviously

variables {C}

@[simp] def of_function {I : Type u₁} (F : I → C) : (discrete I) ⥤ C :=
{ obj := F,
  map' := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end }

end functor

end category_theory

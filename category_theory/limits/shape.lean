-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.types
import category_theory.isomorphism

open category_theory

universes u v w

namespace category_theory.limits

section shapes
structure shape (C : Type u) [𝒞 : category.{u v} C] :=
(X : C)

@[extensionality] lemma shape.ext (C : Type u) [𝒞 : category.{u v} C] (S T : shape C) (h : S.X = T.X) : S = T :=
begin cases S, cases T, obviously end

structure cone {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] (F : J ⥤ C) extends shape C :=
(π : ∀ j : J, X ⟶ F j)
(w' : ∀ {j j' : J} (f : j ⟶ j'), π j ≫ (F.map f) = π j' . obviously)

restate_axiom cone.w'
attribute [simp] cone.w

structure cocone {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] (F : J ⥤ C) extends shape C :=
(ι : ∀ j : J, F j ⟶ X)
(w' : ∀ {j j' : J} (f : j ⟶ j'), (F.map f) ≫ ι j' = ι j . obviously)

restate_axiom cocone.w'
attribute [simp] cocone.w

end shapes

end category_theory.limits

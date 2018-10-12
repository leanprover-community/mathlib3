-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.types
import category_theory.isomorphism

open category_theory

universes u v w

namespace category_theory.limits

definition is_equiv {α β : Type v} (f : α → β) := @is_iso (Type v) (category_theory.types) _ _ f

section shapes
structure shape (C : Type u) [𝒞 : category.{u v} C] :=
(X : C)

@[extensionality] lemma shape.ext (C : Type u) [𝒞 : category.{u v} C] (S T : shape C) (h : S.X = T.X) : S = T :=
begin cases S, cases T, obviously end

structure point (C : Type u) [𝒞 : category.{u v} C] extends shape C.

/--
A `span Y Z`:
`Y <--π₁-- X --π₂--> Z`
-/
structure span {C : Type u} [𝒞 : category.{u v} C] (Y₁ Y₂ : C) extends shape C :=
(π₁ : X ⟶ Y₁)
(π₂ : X ⟶ Y₂)

/--
A `cospan Y Z`:
`Y₁ --ι₁--> X <--ι₂-- Y₂`
-/
structure cospan {C : Type u} [𝒞 : category.{u v} C] (Y₁ Y₂ : C) extends shape C :=
(ι₁ : Y₁ ⟶ X)
(ι₂ : Y₂ ⟶ X)

/--
A `fan f`:
`X --(π b)--> f b`
-/
structure fan {C : Type u} [𝒞 : category.{u v} C] {β : Type v} (f : β → C) extends shape C :=
(π : ∀ b, X ⟶ f b)

/--
A `cofan f`:
`X <--(π b)-- f b`
-/
structure cofan {C : Type u} [𝒞 : category.{u v} C] {β : Type v} (f : β → C) extends shape C :=
(ι : ∀ b, f b ⟶ X)

/--
A `fork f g`:
```
             f
 X --ι--> Y ====> Z
             g
```
-/
structure fork {C : Type u} [𝒞 : category.{u v} C] {Y Z : C} (f g : Y ⟶ Z) extends shape C :=
(ι : X ⟶ Y)
(w' : ι ≫ f = ι ≫ g . obviously)

restate_axiom fork.w'

/--
A `cofork f g`:
```
              f
 X <--π-- Y <==== Z
              g
```
-/
structure cofork {C : Type u} [𝒞 : category.{u v} C] {Y Z : C} (f g : Z ⟶ Y) extends shape C :=
(π : Y ⟶ X)
(w' : f ≫ π = g ≫ π . obviously)

restate_axiom cofork.w'

/--
A `square p q`:
```
X  --π₁--> Y₁
|          |
π₂         r₁
↓          ↓
Y₂ --r₂--> Z
```
-/
structure square {C : Type u} [𝒞 : category.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z)extends shape C :=
(π₁ : X ⟶ Y₁)
(π₂ : X ⟶ Y₂)
(w' : π₁ ≫ r₁ = π₂ ≫ r₂ . obviously)

restate_axiom square.w'

/--
A `cosquare p q`:
```
X  <--ι₁-- Y₁
↑          ↑
ι₂         r₁
|          |
Y₂ <--r₂-- Z
```
-/
structure cosquare {C : Type u} [𝒞 : category.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂)extends shape C :=
(ι₁ : Y₁ ⟶ X)
(ι₂ : Y₂ ⟶ X)
(w' : r₁ ≫ ι₁ = r₂ ≫ ι₂ . obviously)

restate_axiom cosquare.w'

structure cone {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] (F : J ⥤ C) extends shape C :=
(π : ∀ j : J, X ⟶ F j)
(w' : ∀ {j j' : J} (f : j ⟶ j'), π j ≫ (F.map f) = π j' . obviously)

restate_axiom cone.w'

structure cocone {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] (F : J ⥤ C) extends shape C :=
(ι : ∀ j : J, F j ⟶ X)
(w' : ∀ {j j' : J} (f : j ⟶ j'), (F.map f) ≫ ι j' = ι j . obviously)

restate_axiom cocone.w'

end shapes

end category_theory.limits

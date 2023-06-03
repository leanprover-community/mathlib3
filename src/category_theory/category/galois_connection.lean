/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import category_theory.category.preorder
import category_theory.adjunction.basic
import order.galois_connection

/-!

# Galois connections between preorders are adjunctions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `galois_connection.adjunction` is the adjunction associated to a galois connection.

-/

universes u v

section

variables {X : Type u} {Y : Type v} [preorder X] [preorder Y]

/--
A galois connection between preorders induces an adjunction between the associated categories.
-/
def galois_connection.adjunction {l : X → Y} {u : Y → X} (gc : galois_connection l u) :
  gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
category_theory.adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, ⟨λ f, (gc.le_u f.le).hom, λ f, (gc.l_le f.le).hom, by tidy, by tidy⟩ }

end

namespace category_theory

variables {X : Type u} {Y : Type v} [preorder X] [preorder Y]

/--
An adjunction between preorder categories induces a galois connection.
-/
lemma adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) :
  galois_connection L.obj R.obj :=
λ x y, ⟨λ h, ((adj.hom_equiv x y).to_fun h.hom).le, λ h, ((adj.hom_equiv x y).inv_fun h.hom).le⟩

end category_theory

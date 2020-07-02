/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.iso_classes_of_simples
import category_theory.preadditive.schur

open category_theory.limits

namespace category_theory

universes v u w
variables {C : Type u} [category.{v} C]

section
variables [has_zero_morphisms C]

/--
We say a family of objects `Z : ι → C` in a category with zero morphisms is
"mutually simple" if
* for distinct `i j`, every morphism `Z i ⟶ Z j` is zero,
* a morphism `f : Z i ⟶ Z i` is an isomorphism iff it is not zero.

As an example, in a preadditive category with kernels,
any collection of non-isomorphic simple objects is mutually simple (by Schur's lemma).

We abstract out this notion because
1. it's useful to state the definition of Müger semisimplicity
   (which is often used to show that diagrammatic categories are semisimple), and
2. it's the key property needed to diagonalize morphisms between semisimple objects (see below).
-/
structure mutually_simple {ι : Type w} (Z : ι → C) :=
(eq_zero : ∀ {i j} (h : i ≠ j) (f : Z i ⟶ Z j), f = 0)
(simple : Π i (f : Z i ⟶ Z i), is_iso f ≃ (f ≠ 0))

end

section

variables [preadditive C] [has_kernels C]
set_option pp.universes true
/--
In a preadditive category with kernels,
any family of non-isomorphic simple objects is "mutually simple".
-/
def simples_mutually_simple' {ι : Type w} (Z : ι → C)
  [Π i, simple (Z i)] [Π i j, decidable_eq (Z i ⟶ Z j)]
  (w : ∀ {i j} (h : i ≠ j), (Z i ≅ Z j) → false) :
  mutually_simple Z :=
{ eq_zero := λ i j h f,
  begin
    by_contradiction,
    haveI := is_iso_of_hom_simple a,
    exact w h (as_iso f),
  end,
  simple := λ i f, is_iso_equiv_nonzero }

/--
In a preadditive category with kernels,
an arbitrarily chosen representative of each isomorphism class of simples
provides a "mutually simple" family.
-/
noncomputable def simples_mutually_simple [Π i j, decidable_eq (simples C i ⟶ simples C j)] :
  mutually_simple.{v} (simples C) :=
simples_mutually_simple' (simples C) (λ i j, simples_non_isomorphic C)

end

end category_theory

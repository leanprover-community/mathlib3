/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import algebra.homology.homology
import algebra.homology.homotopy

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/

open category_theory
open category_theory.limits

universes v u

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables {c : complex_shape ι} {C D E : homological_complex V c}
  [∀ i, C.has_homology i] [∀ i, D.has_homology i] [∀ i, E.has_homology i]
/--
A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class quasi_iso (f : C ⟶ D) : Prop :=
(is_iso : ∀ i, is_iso (homology_map f i))

attribute [instance] quasi_iso.is_iso

@[priority 100]
instance quasi_iso_of_iso (f : C ⟶ D) [is_iso f] : quasi_iso f :=
{ is_iso := λ i, infer_instance, }

instance quasi_iso_comp (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso g] : quasi_iso (f ≫ g) :=
{ is_iso := λ i, by { rw homology_map_comp, apply_instance, }, }

lemma quasi_iso_of_comp_left (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso (f ≫ g)] :
  quasi_iso g :=
{ is_iso := λ i, is_iso.of_is_iso_fac_left (homology_map_comp f g i).symm, }

lemma quasi_iso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [quasi_iso g] [quasi_iso (f ≫ g)] :
  quasi_iso f :=
{ is_iso := λ i, is_iso.of_is_iso_fac_right (homology_map_comp f g i).symm, }

/-- An homotopy equivalence is a quasi-isomorphism. -/
lemma homotopy_equiv.to_quasi_iso {W : Type*} [category W] [preadditive W]
   {C D : homological_complex W c} (e : homotopy_equiv C D)
   [∀ i, C.has_homology i] [∀ i, D.has_homology i] : quasi_iso e.hom :=
⟨λ i, is_iso.of_iso (e.to_homology_iso i)⟩

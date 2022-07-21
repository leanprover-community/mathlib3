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
variables {V : Type u} [category.{v} V] [has_zero_morphisms V] [has_zero_object V]
variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]
variables {c : complex_shape ι} {C D E : homological_complex V c}

/--
A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class quasi_iso (f : C ⟶ D) : Prop :=
(is_iso : ∀ i, is_iso ((homology_functor V c i).map f))

attribute [instance] quasi_iso.is_iso

@[priority 100]
instance quasi_iso_of_iso (f : C ⟶ D) [is_iso f] : quasi_iso f :=
{ is_iso := λ i, begin
    change is_iso (((homology_functor V c i).map_iso (as_iso f)).hom),
    apply_instance,
  end }

instance quasi_iso_comp (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso g] : quasi_iso (f ≫ g) :=
{ is_iso := λ i, begin
    rw functor.map_comp,
    apply_instance,
  end }

lemma quasi_iso_of_comp_left (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso (f ≫ g)] :
  quasi_iso g :=
{ is_iso := λ i, is_iso.of_is_iso_fac_left ((homology_functor V c i).map_comp f g).symm }

lemma quasi_iso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [quasi_iso g] [quasi_iso (f ≫ g)] :
  quasi_iso f :=
{ is_iso := λ i, is_iso.of_is_iso_fac_right ((homology_functor V c i).map_comp f g).symm }

/-- An homotopy equivalence is a quasi-isomorphism. -/
lemma homotopy_equiv.to_quasi_iso {W : Type*} [category W] [preadditive W]
  [has_cokernels W] [has_images W] [has_equalizers W] [has_zero_object W]
  [has_image_maps W] {C D : homological_complex W c} (e : homotopy_equiv C D) :
  quasi_iso e.hom :=
⟨λ i, begin
  refine ⟨⟨(homology_functor W c i).map e.inv, _⟩⟩,
  simp only [← functor.map_comp, ← (homology_functor W c i).map_id],
  split; apply homology_map_eq_of_homotopy,
  exacts [e.homotopy_hom_inv_id, e.homotopy_inv_hom_id],
end⟩

/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.category.Module.abelian
import algebra.homology.short_exact.abelian
import algebra.category.Module.biproducts

/-!
# Split short exact sequences of modules

These lemmas provide an isomorphism `A × B ≃ₗ[R] M` from a left split or right split short exact
sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`, with the "split exact" condition being expressed in terms of
modules and linear maps without using any category theory.
-/

universes u v
variables {R : Type u} {A M B : Type v} [ring R] [add_comm_group A] [module R A]
  [add_comm_group B] [module R B] [add_comm_group M] [module R M]
open Module

/--The isomorphism `A × B ≃ₗ[R] M` coming from a right split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequiv_prod_of_right_split_exact (j : A →ₗ[R] M) (g : M →ₗ[R] B) (f : B →ₗ[R] M)
  (hj : function.injective j) (exac : j.range = g.ker) (h : g.comp f = linear_map.id) :
  (A × B) ≃ₗ[R] M :=
(({ right_split := ⟨as_hom f, h⟩,
    mono := (mono_iff_injective $ as_hom j).mpr hj,
    exact := (exact_iff _ _).mpr exac } : category_theory.right_split _ _).splitting.iso.trans $
  biprod_iso_prod _ _).to_linear_equiv.symm

/--The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequiv_prod_of_left_split_exact (j : A →ₗ[R] M) (g : M →ₗ[R] B) (f : M →ₗ[R] A)
  (hg : function.surjective g) (exac : j.range = g.ker) (h : f.comp j = linear_map.id) :
  (A × B) ≃ₗ[R] M :=
(({ left_split := ⟨as_hom f, h⟩,
    epi := (epi_iff_surjective $ as_hom g).mpr hg,
    exact := (exact_iff _ _).mpr exac } : category_theory.left_split _ _).splitting.iso.trans $
  biprod_iso_prod _ _).to_linear_equiv.symm

/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homotopy
import algebra.category.Module.abelian
import algebra.category.Module.subobject
import category_theory.limits.concrete_category

/-!
# Complexes of modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide some additional API to work with homological complexes in `Module R`.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {R : Type v} [ring R]
variables {ι : Type*} {c : complex_shape ι} {C D : homological_complex (Module.{u} R) c}

namespace Module

/--
To prove that two maps out of a homology group are equal,
it suffices to check they are equal on the images of cycles.
-/
lemma homology_ext {L M N K : Module R} {f : L ⟶ M} {g : M ⟶ N} (w : f ≫ g = 0)
  {h k : homology f g w ⟶ K}
  (w : ∀ (x : linear_map.ker g),
    h (cokernel.π (image_to_kernel _ _ w) (to_kernel_subobject x)) =
      k (cokernel.π (image_to_kernel _ _ w) (to_kernel_subobject x))) : h = k :=
begin
  refine cokernel_funext (λ n, _),
  -- Gosh it would be nice if `equiv_rw` could directly use an isomorphism, or an enriched `≃`.
  equiv_rw (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).to_linear_equiv.to_equiv at n,
  convert w n; simp [to_kernel_subobject],
end

/-- Bundle an element `C.X i` such that `C.d_from i x = 0` as a term of `C.cycles i`. -/
abbreviation to_cycles {C : homological_complex (Module.{u} R) c}
  {i : ι} (x : linear_map.ker (C.d_from i)) : C.cycles i :=
to_kernel_subobject x

@[ext]
lemma cycles_ext {C : homological_complex (Module.{u} R) c} {i : ι}
  {x y : C.cycles i} (w : (C.cycles i).arrow x = (C.cycles i).arrow y) : x = y :=
begin
  apply_fun (C.cycles i).arrow using (Module.mono_iff_injective _).mp (cycles C i).arrow_mono,
  exact w,
end

local attribute [instance] concrete_category.has_coe_to_sort

@[simp] lemma cycles_map_to_cycles (f : C ⟶ D) {i : ι} (x : linear_map.ker (C.d_from i)) :
  (cycles_map f i) (to_cycles x) = to_cycles ⟨f.f i x.1, by simp [x.2]⟩ :=
by { ext, simp, }

/-- Build a term of `C.homology i` from an element `C.X i` such that `C.d_from i x = 0`. -/
abbreviation to_homology
  {C : homological_complex (Module.{u} R) c} {i : ι} (x : linear_map.ker (C.d_from i)) :
  C.homology i :=
homology.π (C.d_to i) (C.d_from i) _ (to_cycles x)

@[ext]
lemma homology_ext' {M : Module R} (i : ι) {h k : C.homology i ⟶ M}
  (w : ∀ (x : linear_map.ker (C.d_from i)), h (to_homology x) = k (to_homology x)) :
  h = k :=
homology_ext _ w

/-- We give an alternative proof of `homology_map_eq_of_homotopy`,
specialized to the setting of `V = Module R`,
to demonstrate the use of extensionality lemmas for homology in `Module R`. -/
example (f g : C ⟶ D) (h : homotopy f g) (i : ι) :
  (homology_functor (Module.{u} R) c i).map f = (homology_functor (Module.{u} R) c i).map g :=
begin
  -- To check that two morphisms out of a homology group agree, it suffices to check on cycles:
  ext,
  simp only [homology_functor_map, homology.π_map_apply],
  -- To check that two elements are equal mod boundaries, it suffices to exhibit a boundary:
  ext1,
  swap, exact (to_prev i h.hom) x.1,
  -- Moreover, to check that two cycles are equal, it suffices to check their underlying elements:
  ext1,
  simp only [map_add, image_to_kernel_arrow_apply, homological_complex.hom.sq_from_left,
      Module.to_kernel_subobject_arrow, category_theory.limits.kernel_subobject_map_arrow_apply,
      d_next_eq_d_from_from_next, function.comp_app, zero_add, Module.coe_comp,
      linear_map.add_apply, map_zero, subtype.val_eq_coe,
      category_theory.limits.image_subobject_arrow_comp_apply, linear_map.map_coe_ker,
      prev_d_eq_to_prev_d_to, h.comm i, x.2],
  abel
end

end Module

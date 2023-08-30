/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.epi_mono
import algebra.category.Module.kernels
import category_theory.subobject.well_powered
import category_theory.subobject.limits

/-!
# Subobjects in the category of `R`-modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/

open category_theory
open category_theory.subobject
open category_theory.limits

open_locale Module

universes v u

namespace Module
variables {R : Type u} [ring R] (M : Module.{v} R)

/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
    submodules.-/
noncomputable def subobject_Module : subobject M ≃o submodule R M := order_iso.symm
({ inv_fun := λ S, S.arrow.range,
  to_fun := λ N, subobject.mk ↾N.subtype,
  right_inv := λ S, eq.symm
  begin
    fapply eq_mk_of_comm,
    { apply linear_equiv.to_Module_iso'_left,
      apply linear_equiv.of_bijective (linear_map.cod_restrict S.arrow.range S.arrow _),
      split,
      { simpa only [← linear_map.ker_eq_bot, linear_map.ker_cod_restrict]
          using ker_eq_bot_of_mono _ },
      { rw [← linear_map.range_eq_top, linear_map.range_cod_restrict,
          submodule.comap_subtype_self] },
      { exact linear_map.mem_range_self _ } },
    { apply linear_map.ext,
      intros x,
      refl }
  end,
  left_inv := λ N,
  begin
    convert congr_arg linear_map.range (underlying_iso_arrow ↾N.subtype) using 1,
    { have : (underlying_iso ↾N.subtype).inv = (underlying_iso ↾N.subtype).symm.to_linear_equiv,
      { apply linear_map.ext,
        intros x,
        refl },
      rw [this, comp_def, linear_equiv.range_comp] },
    { exact (submodule.range_subtype _).symm }
  end,
  map_rel_iff' := λ S T,
  begin
    refine ⟨λ h, _, λ h, mk_le_mk_of_comm ↟(submodule.of_le h) (by { ext, refl })⟩,
    convert linear_map.range_comp_le_range (of_mk_le_mk _ _ h) ↾T.subtype,
    { simpa only [←comp_def, of_mk_le_mk_comp] using (submodule.range_subtype _).symm },
    { exact (submodule.range_subtype _).symm }
  end })

instance well_powered_Module : well_powered (Module.{v} R) :=
⟨λ M, ⟨⟨_, ⟨(subobject_Module M).to_equiv⟩⟩⟩⟩

local attribute [instance] has_kernels_Module

/-- Bundle an element `m : M` such that `f m = 0` as a term of `kernel_subobject f`. -/
noncomputable def to_kernel_subobject {M N : Module R} {f : M ⟶ N} :
  linear_map.ker f →ₗ[R] kernel_subobject f :=
(kernel_subobject_iso f ≪≫ Module.kernel_iso_ker f).inv

@[simp] lemma to_kernel_subobject_arrow {M N : Module R} {f : M ⟶ N} (x : linear_map.ker f) :
  (kernel_subobject f).arrow (to_kernel_subobject x) = x.1 :=
by simp [to_kernel_subobject]

/--
An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
@[ext]
lemma cokernel_π_image_subobject_ext {L M N : Module.{v} R}
  (f : L ⟶ M) [has_image f] (g : (image_subobject f : Module.{v} R) ⟶ N) [has_cokernel g]
  {x y : N} (l : L) (w : x = y + g (factor_thru_image_subobject f l)) :
  cokernel.π g x = cokernel.π g y :=
by { subst w, simp, }

end Module

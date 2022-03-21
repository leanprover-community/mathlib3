/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.epi_mono
import category_theory.subobject.well_powered

/-!
# Subobjects in the category of `R`-modules

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/

open category_theory
open category_theory.subobject
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

end Module

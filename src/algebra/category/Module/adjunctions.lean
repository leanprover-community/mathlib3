/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import algebra.category.Module.monoidal
import category_theory.monoidal.functorial
import category_theory.monoidal.types
import linear_algebra.direct_sum.finsupp

/-!
The functor of forming finitely supported functions on a type with values in a `[ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

noncomputable theory

universe u

open category_theory

namespace Module

open_locale classical

variables (R : Type u)

section
variables [ring R]

/--
The free functor `Type u ⥤ Module R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
@[simps]
def free : Type u ⥤ Module R :=
{ obj := λ X, Module.of R (X →₀ R),
  map := λ X Y f, finsupp.lmap_domain _ _ f,
  map_id' := by { intros, exact finsupp.lmap_domain_id _ _ },
  map_comp' := by { intros, exact finsupp.lmap_domain_comp _ _ _ _, } }

/--
The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (Module.{u} R) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X M, (finsupp.lift M R X).to_equiv.symm,
  hom_equiv_naturality_left_symm' := λ _ _ M f g,
  finsupp.lhom_ext' (λ x, linear_map.ext_ring
    (finsupp.sum_map_domain_index_add_monoid_hom (λ y, ((smul_add_hom R ↥M).flip) (g y))).symm) }

end

namespace free
variables [comm_ring R]

/-- The free R-module functor is lax monoidal. -/
-- In fact, it's strong monoidal, but we don't yet have a typeclass for that.
instance : lax_monoidal.{u} (free R).obj :=
{ -- Send `R` to `punit →₀ R`
  ε := finsupp.lsingle punit.star,
  -- Send `(α →₀ R) ⊗ (β →₀ R)` to `α × β →₀ R`
  μ := λ α β, (finsupp_tensor_finsupp' R α β).to_linear_map,
  μ_natural' := begin
    intros,
    ext x x' ⟨y, y'⟩,
    -- This is rather tedious: it's a terminal simp, with no arguments,
    -- but between the four of them it is too slow.
    simp only [tensor_product.mk_apply, mul_one, monoidal.tensor_apply, monoidal_category.hom_apply,
      Module.free_map, Module.coe_comp, map_functorial_obj,
      linear_map.compr₂_apply, linear_equiv.coe_to_linear_map, linear_map.comp_apply,
      function.comp_app,
      finsupp.lmap_domain_apply, finsupp.map_domain_single,
      finsupp_tensor_finsupp'_single_tmul_single, finsupp.lsingle_apply],
  end,
  left_unitality' := begin
    intros,
    ext,
    simp only [tensor_product.mk_apply, mul_one,
      Module.id_apply, Module.free_map, Module.coe_comp, map_functorial_obj,
      Module.monoidal_category.hom_apply, monoidal.left_unitor_hom_apply,
      Module.monoidal_category.left_unitor_hom_apply,
      linear_map.compr₂_apply, linear_equiv.coe_to_linear_map, linear_map.comp_apply,
      function.comp_app,
      finsupp.lmap_domain_apply, finsupp.smul_single', finsupp.map_domain_single,
      finsupp_tensor_finsupp'_single_tmul_single, finsupp.lsingle_apply],
  end,
  right_unitality' := begin
    intros,
    ext,
    simp only [tensor_product.mk_apply, mul_one,
      Module.id_apply, Module.free_map, Module.coe_comp, map_functorial_obj,
      Module.monoidal_category.hom_apply, monoidal.right_unitor_hom_apply,
      Module.monoidal_category.right_unitor_hom_apply,
      linear_map.compr₂_apply, linear_equiv.coe_to_linear_map, linear_map.comp_apply,
      function.comp_app,
      finsupp.lmap_domain_apply, finsupp.smul_single', finsupp.map_domain_single,
      finsupp_tensor_finsupp'_single_tmul_single, finsupp.lsingle_apply],
  end,
  associativity' := begin
    intros,
    ext,
    simp only [tensor_product.mk_apply, mul_one,
      Module.id_apply, Module.free_map, Module.coe_comp, map_functorial_obj,
      Module.monoidal_category.hom_apply, monoidal.associator_hom_apply,
      Module.monoidal_category.associator_hom_apply,
      linear_map.compr₂_apply, linear_equiv.coe_to_linear_map, linear_map.comp_apply,
      function.comp_app,
      finsupp.lmap_domain_apply, finsupp.smul_single', finsupp.map_domain_single,
      finsupp_tensor_finsupp'_single_tmul_single, finsupp.lsingle_apply],
  end, }

end free

end Module

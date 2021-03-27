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

section lax_monoidal
variables [comm_ring R]

/-- The free R-module functor is lax monoidal. -/
-- In fact, it's strong monoidal, but we don't yet have a typeclass for that.
instance : lax_monoidal.{u} (free R).obj :=
{ -- Send `R` to `punit →₀ R`
  ε := finsupp.lsingle punit.star,
  -- Send `(α →₀ R) ⊗ (β →₀ R)` to `α × β →₀ R`
  μ := λ α β, (finsupp_tensor_finsupp' R α β).to_linear_map,
  μ_natural' := by { intros, ext x x' ⟨y, y'⟩, simp, },
  left_unitality' := by { intros, ext, simp, },
  right_unitality' := by { intros, ext, simp, },
  associativity' := by { intros, ext, simp, }, }

end lax_monoidal

end Module

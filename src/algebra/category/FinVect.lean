/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.finite_dimensional
import category_theory.monoidal.category
import linear_algebra.finsupp_vector_space
import linear_algebra.dual
import linear_algebra.coevaluation
import .Module.monoidal

/-!
# The category of finite dimensional `R`-modules

-/
noncomputable theory

open category_theory Module.monoidal_category
open_locale classical

universes u

variables (K : Type u) [field K]

namespace FinVect

--TODO decide between this and a new structure extending `Module`.
@[reducible]
def FinVect := { V : Module.{u} K // finite_dimensional K V.carrier }

instance FinVect_category : category (FinVect K) := by apply_instance
instance FinVect_finite_dimensional (V : FinVect K): finite_dimensional K V := V.prop

-- This should go to `linear_algebra.finite_dimensional`.
instance finite_dimensional_tensor_product (V V₂ : Type*) [add_comm_group V]
  [module K V] [add_comm_group V₂] [module K V₂] [finite_dimensional K V] [finite_dimensional K V₂] :
  finite_dimensional K (tensor_product K V V₂) :=
finite_dimensional.of_fintype_basis
  (finsupp.basis.tensor_product (basis.of_vector_space K V) (basis.of_vector_space K V₂))

instance FinVect_monoidal_category : monoidal_category (FinVect K) :=
@monoidal_category.full_monoidal_subcategory _ _ Module.monoidal_category
 (λ (V : Module K), finite_dimensional K V)
 (by { exact finite_dimensional.finite_dimensional_self K})
 (λ X Y hX hY, @FinVect.finite_dimensional_tensor_product K _ X Y _ _ _ _ hX hY)

-- This should go to `linear_algebra.finite_dimensional`.
instance finite_dimensional_dual (V : Type*) [add_comm_group V] [module K V]
  [finite_dimensional K V] :
  finite_dimensional K (module.dual K V) :=
finite_dimensional.of_fintype_basis (basis.dual_basis (basis.of_vector_space K V))

def FinVect_dual (V : FinVect K) : FinVect K :=
⟨Module.of K (module.dual K V), FinVect.finite_dimensional_dual K V.val⟩

open category_theory.monoidal_category

def FinVect_coevaluation (V : FinVect K) : 𝟙_ (FinVect K) ⟶ V ⊗ (FinVect_dual K V) :=
by { haveI := V.prop, change _ →ₗ[K] _, apply coevaluation K V }

def FinVect_evaluation (V : FinVect K) : (FinVect_dual K V) ⊗ V ⟶ 𝟙_ (FinVect K) :=
by { change _ →ₗ[K] _, apply contract_left K V }

set_option profiler true
theorem FinVect_coevaluation_evaluation (V : FinVect K) :
  let V' : FinVect K := FinVect_dual K V in
  (𝟙 V' ⊗ (FinVect_coevaluation K V)) ≫ (α_ V' V V').inv ≫ (FinVect_evaluation K V ⊗ 𝟙 V')
  = (ρ_ V').hom ≫ (λ_ V').inv :=
begin

end


end FinVect

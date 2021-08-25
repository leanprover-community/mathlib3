/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.finite_dimensional
import category_theory.monoidal.category
import linear_algebra.finsupp_vector_space
import .Module.monoidal

/-!
# The category of finite dimensional `R`-modules

-/
open category_theory Module.monoidal_category
open_locale tensor_product

universes v u

variables (K : Type u) [field K]

namespace FinVect

--TODO decide between this and a new structure extending `Module`.
@[reducible]
def FinVect := { V : Module K // finite_dimensional K V }

instance FinVect_category : category (FinVect K) := by apply_instance

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

--TODO prove rigidness

end FinVect

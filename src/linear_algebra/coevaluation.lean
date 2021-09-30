/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.dual
import linear_algebra.finsupp_vector_space
import linear_algebra.finite_dimensional
import linear_algebra.contraction
import linear_algebra.tensor_product_basis

/-!
# The coevaluation map on finite dimensional vector spaces

Given a finite dimensional vector space `V` over a field `K` this describes the canonical linear map
from `K` to `V ⊗ dual K V` which corresponds to the identity function on `V`.

## Tags

coevaluation, dual module, tensor product

## Future work

* Prove that this is independent of the choice of basis on `V`.
-/
noncomputable theory

section coevaluation
open tensor_product finite_dimensional
open_locale tensor_product big_operators

universes u v

variables (K : Type u) [field K]
variables (V : Type v) [add_comm_group V] [module K V] [finite_dimensional K V]

/-- The coevaluation map is a linear map from a field `K` to a finite dimensional
  vector space `V`. -/
def coevaluation : K →ₗ[K] V ⊗[K] (module.dual K V) :=
  let bV := basis.of_vector_space K V in
  (basis.singleton unit K).constr K $
    λ _, ∑ (i : basis.of_vector_space_index K V), bV i ⊗ₜ[K] bV.coord i

lemma coevaluation_apply_one :
 (coevaluation K V) (1 : K) =
   let bV := basis.of_vector_space K V in
   ∑ (i : basis.of_vector_space_index K V), bV i ⊗ₜ[K] bV.coord i :=
begin
  simp only [coevaluation, id],
  rw [(basis.singleton unit K).constr_apply_fintype K],
  simp only [fintype.univ_punit, finset.sum_const, one_smul, basis.singleton_repr,
   basis.equiv_fun_apply,basis.coe_of_vector_space, one_nsmul, finset.card_singleton],
end

open tensor_product

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `category_theory.monoidal.rigid`. -/
lemma contract_left_assoc_coevaluation :
  ((contract_left K V).rtensor _)
   ∘ₗ (tensor_product.assoc K _ _ _).symm.to_linear_map
   ∘ₗ ((coevaluation K V).ltensor (module.dual K V))
  = (tensor_product.lid K _).symm.to_linear_map ∘ₗ (tensor_product.rid K _).to_linear_map :=
begin
  letI := classical.dec_eq (basis.of_vector_space_index K V),
  apply tensor_product.ext,
  apply (basis.of_vector_space K V).dual_basis.ext, intro j, apply linear_map.ext_ring,
  rw [linear_map.compr₂_apply, linear_map.compr₂_apply, tensor_product.mk_apply],
  simp only [linear_map.coe_comp, function.comp_app, linear_equiv.coe_to_linear_map],
  rw [rid_tmul, one_smul, lid_symm_apply],
  simp only [linear_equiv.coe_to_linear_map, linear_map.ltensor_tmul, coevaluation_apply_one],
  rw [tensor_product.tmul_sum, linear_equiv.map_sum], simp only [assoc_symm_tmul],
  rw [linear_map.map_sum], simp only [linear_map.rtensor_tmul, contract_left_apply],
  simp only [basis.coe_dual_basis, basis.coord_apply, basis.repr_self_apply,
    tensor_product.ite_tmul],
  rw [finset.sum_ite_eq'], simp only [finset.mem_univ, if_true]
end

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `category_theory.monoidal.rigid`. -/
lemma contract_left_assoc_coevaluation' :
  ((contract_left K V).ltensor _)
   ∘ₗ (tensor_product.assoc K _ _ _).to_linear_map
   ∘ₗ ((coevaluation K V).rtensor V)
  = (tensor_product.rid K _).symm.to_linear_map ∘ₗ (tensor_product.lid K _).to_linear_map :=
begin
  letI := classical.dec_eq (basis.of_vector_space_index K V),
  apply tensor_product.ext,
  apply linear_map.ext_ring, apply (basis.of_vector_space K V).ext, intro j,
  rw [linear_map.compr₂_apply, linear_map.compr₂_apply, tensor_product.mk_apply],
  simp only [linear_map.coe_comp, function.comp_app, linear_equiv.coe_to_linear_map],
  rw [lid_tmul, one_smul, rid_symm_apply],
  simp only [linear_equiv.coe_to_linear_map, linear_map.rtensor_tmul, coevaluation_apply_one],
  rw [tensor_product.sum_tmul, linear_equiv.map_sum], simp only [assoc_tmul],
  rw [linear_map.map_sum], simp only [linear_map.ltensor_tmul, contract_left_apply],
  simp only [basis.coord_apply, basis.repr_self_apply, tensor_product.tmul_ite],
  rw [finset.sum_ite_eq], simp only [finset.mem_univ, if_true]
end

end coevaluation

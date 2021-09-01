/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.finite_dimensional
import category_theory.monoidal.rigid
import linear_algebra.finsupp_vector_space
import linear_algebra.dual
import linear_algebra.coevaluation
import .Module.monoidal

/-!
# The category of finite dimensional vector spaces

This introduces `FinVect K`, the category of finite dimensional vector spaces on a field `K`.
It is implemented as a full subcategory on a subtype of  `Module K`.
We first create the instance as a category, then as a monoidal category and then as a rigid monoidal
category.

## Future work

* Show that `FinVect K` is a symmetric monoidal category.

-/
noncomputable theory

open category_theory Module.monoidal_category
open_locale classical big_operators

universes u

variables (K : Type u) [field K]

namespace FinVect

--TODO decide between this and a new structure extending `Module`.
def FinVect := { V : Module.{u} K // finite_dimensional K V.carrier }

instance FinVect_category : category (FinVect K) := by unfold FinVect; apply_instance

instance FinVect_finite_dimensional (V : FinVect K): finite_dimensional K V.val := V.prop

instance FinVect_has_sort_coe : has_coe_to_sort (FinVect K) := ⟨_, λ V, V.val⟩

instance FinVect_has_coe_to_fn (V W : FinVect K) : has_coe_to_fun (V ⟶ W) :=
  ⟨λ _, V.val → W.val, λ f, f.to_fun⟩

-- This should go to `linear_algebra` after `linear_algebra` is cleaned up.
-- Right now it cannot go to either `linear_algebra.tensor_product` or `linear_algebra.finite_dimension` because of dependencies.
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

-- This should go to `linear_algebra`.
instance finite_dimensional_dual (V : Type*) [add_comm_group V] [module K V]
  [finite_dimensional K V] :
  finite_dimensional K (module.dual K V) :=
finite_dimensional.of_fintype_basis (basis.dual_basis (basis.of_vector_space K V))

variables (V : FinVect K)

def FinVect_dual : FinVect K :=
⟨Module.of K (module.dual K V.val), FinVect.finite_dimensional_dual K V.val⟩

open category_theory.monoidal_category

def FinVect_coevaluation : 𝟙_ (FinVect K) ⟶ V ⊗ (FinVect_dual K V) :=
by { haveI := V.prop, change _ →ₗ[K] _, apply coevaluation K V.val }

lemma FinVect_coevaluation_apply :
 (FinVect_coevaluation K V) (1 : K) =
   let bV := basis.of_vector_space K V.val in
   ∑ (i : basis.of_vector_space_index K V.val), bV i ⊗ₜ[K] bV.coord i :=
begin
  simp only [FinVect_coevaluation, coevaluation, id],
  rw [(basis.singleton unit K).constr_apply_fintype K],
  simp only [fintype.univ_punit, finset.sum_const, one_smul, basis.singleton_repr,
   basis.equiv_fun_apply,basis.coe_of_vector_space, one_nsmul, finset.card_singleton],
end

/-- The evaluation morphism is given by the contraction map. -/
def FinVect_evaluation : (FinVect_dual K V) ⊗ V ⟶ 𝟙_ (FinVect K) :=
(contract_left K V.val : _ →ₗ[K] _)

lemma FinVect_evaluation_apply (f : (FinVect_dual K V).val) (x : V.val) :
  (FinVect_evaluation K V) (f ⊗ₜ x) = by { change K, change _ →ₗ[K] _ at f, exact f x } :=
by { simp only [FinVect_evaluation, id], apply contract_left_apply f x }

@[simp]
lemma right_unitor_hom_apply_tensor_one (x : V.val) :
  ((ρ_ V).hom : _ →ₗ[K] _) (x ⊗ₜ[K] (1 : K)) = x :=
(right_unitor_hom_apply x 1).trans (one_smul _ _)

@[simp]
lemma left_unitor_hom_apply_one_tensor (x : V.val) :
  ((λ_ V).hom : _ →ₗ[K] _) ((1 : K) ⊗ₜ[K] x) = x :=
(left_unitor_hom_apply 1 x).trans (one_smul _ _)

@[simp]
lemma left_unitor_inv_apply (x : V.val) :
  ((λ_ V).inv : _ →ₗ[K] _) x = (1 : K) ⊗ₜ[K] x :=
left_unitor_inv_apply _

@[simp]
lemma right_unitor_inv_apply (x : V.val) :
  ((ρ_ V).inv : _ →ₗ[K] _) x = x ⊗ₜ[K] (1 : K) :=
right_unitor_inv_apply _

@[simp]
lemma tensor_hom_apply {U V W X : FinVect K} (f : U ⟶ V) (g : W ⟶ X) (k : U.val) (m : W.val) :
  ((f ⊗ g) : U ⊗ W ⟶ V ⊗ X) (k ⊗ₜ m) = f k ⊗ₜ g m :=
hom_apply f g k m

@[simp]
lemma id_apply {V : FinVect K} (x : V.val) : (𝟙 V : _ →ₗ[K] _) x = x := rfl

@[simp]
lemma associator_inv_apply {U V W : FinVect K} (u : U.val) (v : V.val) (w : W.val) :
  ((α_ U V W).inv : U ⊗ (V ⊗ W) ⟶ (U ⊗ V) ⊗ W) (u ⊗ₜ (v ⊗ₜ w)) = ((u ⊗ₜ v) ⊗ₜ w) :=
associator_inv_apply u v w

@[simp]
lemma associator_hom_apply {U V W : FinVect K} (u : U.val) (v : V.val) (w : W.val) :
  ((α_ U V W).hom : (U ⊗ V) ⊗ W ⟶ U ⊗ (V ⊗ W)) ((u ⊗ₜ v) ⊗ₜ w) = (u ⊗ₜ (v ⊗ₜ w)) :=
associator_hom_apply u v w

private theorem coevaluation_evaluation :
  let V' : FinVect K := FinVect_dual K V in
  (𝟙 V' ⊗ (FinVect_coevaluation K V)) ≫ (α_ V' V V').inv ≫ (FinVect_evaluation K V ⊗ 𝟙 V')
  = (ρ_ V').hom ≫ (λ_ V').inv :=
begin
  apply tensor_product.mk_compr₂_inj,
  apply (basis.of_vector_space K V.val).dual_basis.ext, intro j, apply linear_map.ext_ring,
  rw [linear_map.compr₂_apply, linear_map.compr₂_apply],
  simp only [tensor_product.mk_apply, basis.coe_dual_basis],
  erw [linear_map.coe_comp, linear_map.coe_comp, linear_map.coe_comp],
  rw [function.comp_app, function.comp_app, function.comp_app],
  erw [right_unitor_hom_apply_tensor_one K, left_unitor_inv_apply K, tensor_hom_apply K],
  rw [id_apply, FinVect_coevaluation_apply K V, tensor_product.tmul_sum],
  simp only [linear_map.map_sum, linear_map.to_fun_eq_coe],
  conv_lhs { congr, skip, funext,
    rw [associator_inv_apply K, tensor_hom_apply K, id_apply K, FinVect_evaluation_apply,
     id.def, id.def, basis.coord_apply, (basis.of_vector_space K ↥(V.val)).repr_self_apply,
     tensor_product.ite_tmul] },
  rw [finset.sum_ite_eq'], simp only [finset.mem_univ, if_true]
end

private theorem evaluation_coevaluation :
  (FinVect_coevaluation K V ⊗ 𝟙 V)
  ≫ (α_ V (FinVect_dual K V) V).hom ≫ (𝟙 V ⊗ FinVect_evaluation K V)
  = (λ_ V).hom ≫ (ρ_ V).inv :=
begin
  apply tensor_product.mk_compr₂_inj,
  apply linear_map.ext_ring, apply (basis.of_vector_space K V.val).ext, intro j,
  rw [linear_map.compr₂_apply, linear_map.compr₂_apply],
  simp only [tensor_product.mk_apply, basis.coe_dual_basis],
  erw [linear_map.coe_comp, linear_map.coe_comp, linear_map.coe_comp],
  rw [function.comp_app, function.comp_app, function.comp_app],
  erw [left_unitor_hom_apply_one_tensor K, right_unitor_inv_apply K, tensor_hom_apply K],
  rw [id_apply, FinVect_coevaluation_apply K V, tensor_product.sum_tmul],
  simp only [linear_map.map_sum, linear_map.to_fun_eq_coe],
  conv_lhs { congr, skip, funext,
    rw [associator_hom_apply K, tensor_hom_apply K, id_apply K, FinVect_evaluation_apply,
     id.def, id.def, basis.coord_apply, (basis.of_vector_space K ↥(V.val)).repr_self_apply,
     tensor_product.tmul_ite] },
  rw [finset.sum_ite_eq], simp only [finset.mem_univ, if_true]
end

instance exact_pairing : exact_pairing V (FinVect_dual K V) :=
{ coevaluation := FinVect_coevaluation K V,
  evaluation := FinVect_evaluation K V,
  coevaluation_evaluation' := coevaluation_evaluation K V,
  evaluation_coevaluation' := evaluation_coevaluation K V }

instance right_dual : has_right_dual V := ⟨FinVect_dual K V⟩

instance right_rigid_category : right_rigid_category (FinVect K) := { }

end FinVect

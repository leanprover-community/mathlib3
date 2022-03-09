/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
import linear_algebra.dual
import linear_algebra.matrix.to_lin
import linear_algebra.tensor_product_basis
import linear_algebra.free_module.finite.rank

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

section contraction

open tensor_product linear_map matrix
open_locale tensor_product big_operators

variables (R M N : Type*) [add_comm_group M] [add_comm_group N]

section comm_ring

variables [comm_ring R] [module R M] [module R N]
variables {ι : Type*} [decidable_eq ι] [fintype ι] (b : basis ι R M)

/-- The natural left-handed pairing between a module and its dual. -/
def contract_left : (module.dual R M) ⊗ M →ₗ[R] R := (uncurry _ _ _ _).to_fun linear_map.id

/-- The natural right-handed pairing between a module and its dual. -/
def contract_right : M ⊗ (module.dual R M) →ₗ[R] R :=
(uncurry _ _ _ _).to_fun (linear_map.flip linear_map.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dual_tensor_hom : (module.dual R M) ⊗ N →ₗ[R] M →ₗ[R] N :=
  let M' := module.dual R M in
  (uncurry R M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) linear_map.smul_rightₗ

/-- An explicit inverse of `dual_tensor_hom` given a basis. -/
noncomputable def hom_dual_tensor : (M →ₗ[R] N) →ₗ[R] (module.dual R M) ⊗[R] N :=
∑ i, (tensor_product.mk R _ N (b.dual_basis i)) ∘ₗ linear_map.applyₗ (b i)

lemma hom_dual_tensor_apply (f : M →ₗ[R] N) :
  hom_dual_tensor R M N b f = ∑ i, b.dual_basis i ⊗ₜ f (b i) :=
linear_map.sum_apply _ _ _

variables {R M N}

@[simp] lemma contract_left_apply (f : module.dual R M) (m : M) :
  contract_left R M (f ⊗ₜ m) = f m := by apply uncurry_apply

@[simp] lemma contract_right_apply (f : module.dual R M) (m : M) :
  contract_right R M (m ⊗ₜ f) = f m := by apply uncurry_apply

@[simp] lemma dual_tensor_hom_apply (f : module.dual R M) (m : M) (n : N) :
  dual_tensor_hom R M N (f ⊗ₜ n) m = (f m) • n :=
by { dunfold dual_tensor_hom, rw uncurry_apply, refl, }

/-- As a matrix, `dual_tensor_hom` evaluated on a basis element of `M* ⊗ N` is a matrix with a
single one and zeros elsewhere -/
theorem to_matrix_dual_tensor_hom
  {m : Type*} {n : Type*} [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  (bM : basis m R M) (bN : basis n R N) (j : m) (i : n) :
    to_matrix bM bN (dual_tensor_hom R M N (bM.coord j ⊗ₜ bN i)) = std_basis_matrix i j 1 :=
begin
  ext i' j',
  by_cases hij : (i = i' ∧ j = j');
  simp [linear_map.to_matrix_apply, finsupp.single_eq_pi_single, hij],
  rw [and_iff_not_or_not, not_not] at hij, cases hij; simp [hij],
end

/-- `hom_dual_tensor` is right inverse to `dual_tensor_hom` -/
@[simp]
lemma dual_tensor_hom_hom_dual_tensor_apply (f : M →ₗ[R] N):
  (dual_tensor_hom R M N) ((hom_dual_tensor R M N b) f) = f :=
begin
  ext m, nth_rewrite_rhs 0 ←basis.sum_repr b m,
  simp [hom_dual_tensor],
end

/-- `hom_dual_tensor` is right inverse to `dual_tensor_hom` -/
lemma dual_tensor_hom_hom_dual_tensor :
  (dual_tensor_hom R M N) ∘ₗ (hom_dual_tensor R M N b) = id :=
by { ext f, simp }

local attribute [ext] tensor_product.ext

lemma hom_dual_tensor_dual_tensor_hom :
  hom_dual_tensor R M N b ∘ₗ dual_tensor_hom R M N = linear_map.id :=
begin
  ext f m,
  show hom_dual_tensor R M N b (dual_tensor_hom R M N (f ⊗ₜ[R] m)) = f ⊗ₜ[R] m,
  simp_rw [hom_dual_tensor_apply, dual_tensor_hom_apply f _ m, ←smul_tmul, ←sum_tmul,
    basis.coe_dual_basis, basis.sum_dual_apply_smul_coord],
end

/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
@[simps] noncomputable def dual_tensor_hom_equiv_of_basis :
  (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
linear_equiv.of_linear (dual_tensor_hom R M N) (hom_dual_tensor R M N b)
  (dual_tensor_hom_hom_dual_tensor b) (hom_dual_tensor_dual_tensor_hom b)

@[simp] lemma dual_tensor_hom_equiv_of_basis_to_linear_map :
  (dual_tensor_hom_equiv_of_basis b : (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N).to_linear_map =
  dual_tensor_hom R M N :=
rfl

end comm_ring

section field

variables [field R] [module R M] [module R N] [finite_dimensional R M]

/-- If `M` is finite-dimensional over a field, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp] noncomputable def dual_tensor_hom_equiv : (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
dual_tensor_hom_equiv_of_basis (finite_dimensional.fin_basis R M)

end field

end contraction

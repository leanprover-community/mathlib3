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

universes u v


section contraction

open tensor_product
open linear_map
open matrix
open_locale tensor_product
open_locale big_operators

section

variables (R : Type u) (M N : Type v)
variables [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]

/-- The natural left-handed pairing between a module and its dual. -/
def contract_left : (module.dual R M) ⊗ M →ₗ[R] R := (uncurry _ _ _ _).to_fun linear_map.id

/-- The natural right-handed pairing between a module and its dual. -/
def contract_right : M ⊗ (module.dual R M) →ₗ[R] R :=
(uncurry _ _ _ _).to_fun (linear_map.flip linear_map.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dual_tensor_hom : (module.dual R M) ⊗ N →ₗ[R] M →ₗ[R] N :=
  let M' := module.dual R M in
  (uncurry R M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) linear_map.smul_rightₗ

/-- An explicit right inverse of `dual_tensor_hom` given a basis. -/
noncomputable def hom_dual_tensor
  {ι : Type*} [fintype ι] [decidable_eq ι] (b : basis ι R M) :
  (M →ₗ[R] N) →ₗ[R] (module.dual R M) ⊗[R] N :=
∑ i, (tensor_product.mk R _ N (b.dual_basis i)) ∘ₗ linear_map.applyₗ (b i)

lemma hom_dual_tensor_apply
  {ι : Type*} [fintype ι] [decidable_eq ι] (b : basis ι R M) (f : M →ₗ[R] N) :
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
theorem dual_tensor_hom_basis
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
lemma dual_tensor_hom_hom_dual_tensor_apply
  {ι : Type} [fintype ι] [decidable_eq ι] (b : basis ι R M) (f : M →ₗ[R] N):
  (dual_tensor_hom R M N) ((hom_dual_tensor R M N b) f) = f :=
begin
  ext m, nth_rewrite_rhs 0 ←basis.sum_repr b m,
  simp [hom_dual_tensor],
end

/-- `hom_dual_tensor` is right inverse to `dual_tensor_hom` -/
lemma dual_tensor_hom_hom_dual_tensor {ι : Type} [fintype ι] [decidable_eq ι] (b : basis ι R M):
  (dual_tensor_hom R M N) ∘ₗ (hom_dual_tensor R M N b) = id :=
by { ext f, simp }

/-- `hom_dual_tensor` is left inverse to `dual_tensor_hom` -/
lemma hom_dual_tensor_dual_tensor_hom {ι : Type} [fintype ι] [decidable_eq ι] (b : basis ι R M):
  (hom_dual_tensor R M N b) ∘ₗ (dual_tensor_hom R M N) = id :=
begin
  apply curry_injective,
  apply basis.ext b.dual_basis,
  intro i, ext n,
  --simp [hom_dual_tensor_apply],
end

end

open finite_dimensional
variables (R : Type u) (M N : Type v)
variables [field R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
variables [finite_dimensional R M]

theorem dual_tensor_hom_surj : function.surjective (dual_tensor_hom R M N) :=
begin
  intro f,
  have b := fin_basis R M,
  use hom_dual_tensor R M N b f,
  exact dual_tensor_hom_hom_dual_tensor_apply b f,
end

variables [finite_dimensional R N]

theorem dual_tensor_hom_inj : function.injective (dual_tensor_hom R M N) :=
  (injective_iff_surjective_of_finrank_eq_finrank (by simp)).2 (dual_tensor_hom_surj R M N)

/-- `dual_tensor_hom` is an equivalence -/
noncomputable def dual_tensor_hom_equiv : (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  linear_equiv.of_bijective (dual_tensor_hom R M N)
    (dual_tensor_hom_inj R M N) (dual_tensor_hom_surj R M N)

lemma coe_dual_tensor_hom_equiv :
  (dual_tensor_hom_equiv R M N : (module.dual R M) ⊗[R] N → M →ₗ[R] N) = dual_tensor_hom R M N :=
rfl

@[simp] lemma coe_dual_tensor_hom_equiv_to_linear :
  (dual_tensor_hom_equiv R M N : (module.dual R M) ⊗[R] N →ₗ[R] M →ₗ[R] N)
  = dual_tensor_hom R M N := rfl

@[simp] lemma dual_tensor_hom_equiv_apply (f : (module.dual R M) ⊗[R] N):
  (dual_tensor_hom_equiv R M N) f = (dual_tensor_hom R M N) f := rfl

/-- `hom_dual_tensor` is equal to the inverse of `dual_tensor_hom`, no matter the basis used-/
lemma dual_tensor_hom_equiv_symm
  {ι : Type} [fintype ι] [decidable_eq ι] (b : basis ι R M) :
  ⇑(dual_tensor_hom_equiv R M N).symm = hom_dual_tensor R M N b :=
begin
  apply @function.left_inverse.eq_right_inverse _ _ (dual_tensor_hom_equiv R M N) _ _,
  { apply equiv.left_inverse_symm },
  simp [function.right_inverse, function.left_inverse],
end

end contraction

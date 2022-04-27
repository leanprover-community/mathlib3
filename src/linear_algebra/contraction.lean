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

local attribute [ext] tensor_product.ext

variables (R M N P Q : Type*) [add_comm_group M]
variables [add_comm_group N] [add_comm_group P] [add_comm_group Q]

section comm_ring

variables [comm_ring R] [module R M] [module R N] [module R P] [module R Q]
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

variables {R M N P Q}

@[simp] lemma contract_left_apply (f : module.dual R M) (m : M) :
  contract_left R M (f ⊗ₜ m) = f m := by apply uncurry_apply

@[simp] lemma contract_right_apply (f : module.dual R M) (m : M) :
  contract_right R M (m ⊗ₜ f) = f m := by apply uncurry_apply

@[simp] lemma dual_tensor_hom_apply (f : module.dual R M) (m : M) (n : N) :
  dual_tensor_hom R M N (f ⊗ₜ n) m = (f m) • n :=
by { dunfold dual_tensor_hom, rw uncurry_apply, refl, }

lemma map_dual_tensor_hom (f : module.dual R M) (p : P) (g : module.dual R N) (q : Q) :
  tensor_product.map (dual_tensor_hom R M P (f ⊗ₜ[R] p)) (dual_tensor_hom R N Q (g ⊗ₜ[R] q)) =
  dual_tensor_hom R (M ⊗[R] N) (P ⊗[R] Q) (dual_tensor_dual_map (f ⊗ₜ g) ⊗ₜ[R] (p ⊗ₜ[R] q)) :=
begin
  ext m n, simp only [compr₂_apply, mk_apply, map_tmul, dual_tensor_hom_apply,
  dual_tensor_dual_map_apply, mul_smul_tmul],
end

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

/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
@[simps]
noncomputable def dual_tensor_hom_equiv_of_basis :
  (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
linear_equiv.of_linear
  (dual_tensor_hom R M N)
  (∑ i, (tensor_product.mk R _ N (b.dual_basis i)) ∘ₗ linear_map.applyₗ (b i))
  (begin
    ext f m,
    simp only [applyₗ_apply_apply, coe_fn_sum, dual_tensor_hom_apply, mk_apply, id_coe, id.def,
      fintype.sum_apply, function.comp_app, basis.coe_dual_basis, coe_comp,
      basis.coord_apply, ← f.map_smul, (dual_tensor_hom R M N).map_sum, ← f.map_sum, b.sum_repr],
  end)
  (begin
    ext f m,
    simp only [applyₗ_apply_apply, coe_fn_sum, dual_tensor_hom_apply, mk_apply, id_coe, id.def,
      fintype.sum_apply, function.comp_app, basis.coe_dual_basis, coe_comp,
      compr₂_apply, tmul_smul, smul_tmul', ← sum_tmul, basis.sum_dual_apply_smul_coord],
end)

@[simp] lemma dual_tensor_hom_equiv_of_basis_to_linear_map :
  (dual_tensor_hom_equiv_of_basis b : (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N).to_linear_map =
  dual_tensor_hom R M N :=
rfl

variables (R M N P Q)

variables [module.free R M] [module.finite R M] [nontrivial R]

open_locale classical

/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp] noncomputable def dual_tensor_hom_equiv : (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
dual_tensor_hom_equiv_of_basis (module.free.choose_basis R M)

variables [module.free R N] [module.finite R N]

open module

variables [module.finite R (M ⊗[R] N)] --Temporary until this is made an instance by #13705

/--
When `M` and `N` are free `R` modules, the map `hom_tensor_hom_map` is an equivalence. Note that
`hom_tensor_hom_equiv` is not defined directly in terms of `hom_tensor_hom_map`, but the equivalence
between the two is given by `hom_tensor_hom_equiv_to_linear_map` and `hom_tensor_hom_equiv_apply`.
-/
noncomputable
def hom_tensor_hom_equiv : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
  congr (dual_tensor_hom_equiv R M P).symm (dual_tensor_hom_equiv R N Q).symm ≪≫ₗ
  tensor_tensor_tensor_comm R (dual R M) P (dual R N) Q ≪≫ₗ
  tensor_product.congr dual_tensor_dual_equiv (linear_equiv.refl R (P ⊗ Q)) ≪≫ₗ
  dual_tensor_hom_equiv R (M ⊗ N) (P ⊗ Q)

@[simp]
lemma hom_tensor_hom_equiv_to_linear_map :
  (hom_tensor_hom_equiv R M N P Q).to_linear_map = hom_tensor_hom_map :=
begin
  refine (linear_map.cancel_right
  (congr (dual_tensor_hom_equiv R M P) (dual_tensor_hom_equiv R N Q)).surjective).1 _,
  show (hom_tensor_hom_equiv R M N P Q).to_linear_map ∘ₗ
    (congr (dual_tensor_hom_equiv R M P) (dual_tensor_hom_equiv R N Q)).to_linear_map =
    hom_tensor_hom_map ∘ₗ
    (congr (dual_tensor_hom_equiv R M P) (dual_tensor_hom_equiv R N Q)).to_linear_map,
  ext f p g q m n,
  simp only [dual_tensor_hom_equiv, compr₂_apply, mk_apply, coe_comp,
  linear_equiv.coe_to_linear_map, function.comp_app, congr_tmul, hom_tensor_hom_map_apply,
  map_tmul, dual_tensor_hom_apply, tmul_smul, hom_tensor_hom_equiv, dual_tensor_hom_equiv,
  dual_tensor_dual_equiv, linear_equiv.trans_apply, congr_tmul, linear_equiv.symm_apply_apply,
  tensor_tensor_tensor_comm_tmul, linear_equiv.refl_apply],
  simp only [dual_tensor_hom_equiv_of_basis_apply, dual_tensor_hom_apply,
  dual_tensor_dual_equiv_of_basis_apply_apply, hom_tensor_hom_map_apply, map_tmul, lid_tmul,
  algebra.id.smul_eq_mul, mul_smul_tmul],
end

variables {R M N P Q}

@[simp]
lemma hom_tensor_hom_equiv_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
  hom_tensor_hom_equiv R M N P Q x = hom_tensor_hom_map x :=
by rw [←linear_equiv.coe_to_linear_map, hom_tensor_hom_equiv_to_linear_map]

end comm_ring

end contraction

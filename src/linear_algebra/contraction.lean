/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
import linear_algebra.dual
import linear_algebra.matrix.to_lin

/-!
# Contractions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

variables {ι : Type*} (R M N P Q : Type*)

local attribute [ext] tensor_product.ext

section contraction

open tensor_product linear_map matrix module
open_locale tensor_product big_operators

section comm_semiring
variables [comm_semiring R]
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
variables [module R M] [module R N] [module R P] [module R Q]
variables [decidable_eq ι] [fintype ι] (b : basis ι R M)

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
  contract_left R M (f ⊗ₜ m) = f m := rfl

@[simp] lemma contract_right_apply (f : module.dual R M) (m : M) :
  contract_right R M (m ⊗ₜ f) = f m := rfl

@[simp] lemma dual_tensor_hom_apply (f : module.dual R M) (m : M) (n : N) :
  dual_tensor_hom R M N (f ⊗ₜ n) m = (f m) • n :=
rfl

@[simp] lemma transpose_dual_tensor_hom (f : module.dual R M) (m : M) :
  dual.transpose (dual_tensor_hom R M M (f ⊗ₜ m)) = dual_tensor_hom R _ _ (dual.eval R M m ⊗ₜ f) :=
by { ext f' m', simp only [dual.transpose_apply, coe_comp, function.comp_app, dual_tensor_hom_apply,
  linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, dual.eval_apply, smul_apply],
  exact mul_comm _ _ }

@[simp] lemma dual_tensor_hom_prod_map_zero (f : module.dual R M) (p : P) :
  ((dual_tensor_hom R M P) (f ⊗ₜ[R] p)).prod_map (0 : N →ₗ[R] Q) =
  dual_tensor_hom R (M × N) (P × Q) ((f ∘ₗ fst R M N) ⊗ₜ inl R P Q p) :=
by {ext; simp only [coe_comp, coe_inl, function.comp_app, prod_map_apply, dual_tensor_hom_apply,
fst_apply, prod.smul_mk, zero_apply, smul_zero]}

@[simp] lemma zero_prod_map_dual_tensor_hom (g : module.dual R N) (q : Q) :
  (0 : M →ₗ[R] P).prod_map ((dual_tensor_hom R N Q) (g ⊗ₜ[R] q)) =
  dual_tensor_hom R (M × N) (P × Q) ((g ∘ₗ snd R M N) ⊗ₜ inr R P Q q) :=
by {ext; simp only [coe_comp, coe_inr, function.comp_app, prod_map_apply, dual_tensor_hom_apply,
  snd_apply, prod.smul_mk, zero_apply, smul_zero]}

lemma map_dual_tensor_hom (f : module.dual R M) (p : P) (g : module.dual R N) (q : Q) :
  tensor_product.map (dual_tensor_hom R M P (f ⊗ₜ[R] p)) (dual_tensor_hom R N Q (g ⊗ₜ[R] q)) =
  dual_tensor_hom R (M ⊗[R] N) (P ⊗[R] Q) (dual_distrib R M N (f ⊗ₜ g) ⊗ₜ[R] (p ⊗ₜ[R] q)) :=
begin
  ext m n, simp only [compr₂_apply, mk_apply, map_tmul, dual_tensor_hom_apply,
  dual_distrib_apply, ←smul_tmul_smul],
end

@[simp] lemma comp_dual_tensor_hom (f : module.dual R M) (n : N) (g : module.dual R N) (p : P) :
  (dual_tensor_hom R N P (g ⊗ₜ[R] p)) ∘ₗ (dual_tensor_hom R M N (f ⊗ₜ[R] n)) =
  g n • dual_tensor_hom R M P (f ⊗ₜ p) :=
begin
  ext m, simp only [coe_comp, function.comp_app, dual_tensor_hom_apply, linear_map.map_smul,
                    ring_hom.id_apply, smul_apply], rw smul_comm,
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

end comm_semiring

section comm_ring
variables [comm_ring R]
variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
variables [module R M] [module R N] [module R P] [module R Q]
variables [decidable_eq ι] [fintype ι] (b : basis ι R M)

variables {R M N P Q}

/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
@[simps apply]
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

@[simp] lemma dual_tensor_hom_equiv_of_basis_symm_cancel_left (x : (module.dual R M) ⊗[R] N) :
  (dual_tensor_hom_equiv_of_basis b).symm (dual_tensor_hom R M N x) = x :=
by rw [←dual_tensor_hom_equiv_of_basis_apply b, linear_equiv.symm_apply_apply]

@[simp] lemma dual_tensor_hom_equiv_of_basis_symm_cancel_right (x : M →ₗ[R] N) :
  dual_tensor_hom R M N ((dual_tensor_hom_equiv_of_basis b).symm x)  = x :=
by rw [←dual_tensor_hom_equiv_of_basis_apply b, linear_equiv.apply_symm_apply]

variables (R M N P Q)

variables [module.free R M] [module.finite R M] [nontrivial R]

open_locale classical

/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp] noncomputable def dual_tensor_hom_equiv : (module.dual R M) ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
dual_tensor_hom_equiv_of_basis (module.free.choose_basis R M)

end comm_ring

end contraction

section hom_tensor_hom

open_locale tensor_product

open module tensor_product linear_map

section comm_ring

variables [comm_ring R]
variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
variables [module R M] [module R N] [module R P] [module R Q]
variables [free R M] [finite R M] [free R N] [finite R N] [nontrivial R]

/-- When `M` is a finite free module, the map `ltensor_hom_to_hom_ltensor` is an equivalence. Note
that `ltensor_hom_equiv_hom_ltensor` is not defined directly in terms of
`ltensor_hom_to_hom_ltensor`, but the equivalence between the two is given by
`ltensor_hom_equiv_hom_ltensor_to_linear_map` and `ltensor_hom_equiv_hom_ltensor_apply`. -/
noncomputable def ltensor_hom_equiv_hom_ltensor : P ⊗[R] (M →ₗ[R] Q) ≃ₗ[R] (M →ₗ[R] P ⊗[R] Q) :=
congr (linear_equiv.refl R P) (dual_tensor_hom_equiv R M Q).symm ≪≫ₗ
  tensor_product.left_comm R P _ Q ≪≫ₗ dual_tensor_hom_equiv R M _

/-- When `M` is a finite free module, the map `rtensor_hom_to_hom_rtensor` is an equivalence. Note
that `rtensor_hom_equiv_hom_rtensor` is not defined directly in terms of
`rtensor_hom_to_hom_rtensor`, but the equivalence between the two is given by
`rtensor_hom_equiv_hom_rtensor_to_linear_map` and `rtensor_hom_equiv_hom_rtensor_apply`. -/
noncomputable def rtensor_hom_equiv_hom_rtensor : (M →ₗ[R] P) ⊗[R] Q ≃ₗ[R] (M →ₗ[R] P ⊗[R] Q) :=
congr (dual_tensor_hom_equiv R M P).symm (linear_equiv.refl R Q) ≪≫ₗ
  tensor_product.assoc R _ P Q ≪≫ₗ dual_tensor_hom_equiv R M _

@[simp] lemma ltensor_hom_equiv_hom_ltensor_to_linear_map :
  (ltensor_hom_equiv_hom_ltensor R M P Q).to_linear_map = ltensor_hom_to_hom_ltensor R M P Q :=
begin
  let e := congr (linear_equiv.refl R P) (dual_tensor_hom_equiv R M Q),
  have h : function.surjective e.to_linear_map := e.surjective,
  refine (cancel_right h).1 _,
  ext p f q m,
  dsimp [ltensor_hom_equiv_hom_ltensor],
  simp only [ltensor_hom_equiv_hom_ltensor, dual_tensor_hom_equiv, compr₂_apply, mk_apply, coe_comp,
  linear_equiv.coe_to_linear_map, function.comp_app, map_tmul, linear_equiv.coe_coe,
  dual_tensor_hom_equiv_of_basis_apply, linear_equiv.trans_apply, congr_tmul,
  linear_equiv.refl_apply, dual_tensor_hom_equiv_of_basis_symm_cancel_left, left_comm_tmul,
  dual_tensor_hom_apply, ltensor_hom_to_hom_ltensor_apply, tmul_smul],
end

@[simp] lemma rtensor_hom_equiv_hom_rtensor_to_linear_map :
  (rtensor_hom_equiv_hom_rtensor R M P Q).to_linear_map = rtensor_hom_to_hom_rtensor R M P Q :=
begin
  let e := congr (dual_tensor_hom_equiv R M P) (linear_equiv.refl R Q),
  have h : function.surjective e.to_linear_map := e.surjective,
  refine (cancel_right h).1 _,
  ext f p q m,
  simp only [rtensor_hom_equiv_hom_rtensor, dual_tensor_hom_equiv, compr₂_apply, mk_apply, coe_comp,
  linear_equiv.coe_to_linear_map, function.comp_app, map_tmul, linear_equiv.coe_coe,
  dual_tensor_hom_equiv_of_basis_apply, linear_equiv.trans_apply, congr_tmul,
  dual_tensor_hom_equiv_of_basis_symm_cancel_left, linear_equiv.refl_apply, assoc_tmul,
  dual_tensor_hom_apply, rtensor_hom_to_hom_rtensor_apply, smul_tmul'],
end

variables {R M N P Q}

@[simp] lemma ltensor_hom_equiv_hom_ltensor_apply (x : P ⊗[R] (M →ₗ[R] Q)) :
  ltensor_hom_equiv_hom_ltensor R M P Q x = ltensor_hom_to_hom_ltensor R M P Q x :=
by rw [←linear_equiv.coe_to_linear_map, ltensor_hom_equiv_hom_ltensor_to_linear_map]

@[simp] lemma rtensor_hom_equiv_hom_rtensor_apply (x : (M →ₗ[R] P) ⊗[R] Q) :
  rtensor_hom_equiv_hom_rtensor R M P Q x = rtensor_hom_to_hom_rtensor R M P Q x :=
by rw [←linear_equiv.coe_to_linear_map, rtensor_hom_equiv_hom_rtensor_to_linear_map]

variables (R M N P Q)

/--
When `M` and `N` are free `R` modules, the map `hom_tensor_hom_map` is an equivalence. Note that
`hom_tensor_hom_equiv` is not defined directly in terms of `hom_tensor_hom_map`, but the equivalence
between the two is given by `hom_tensor_hom_equiv_to_linear_map` and `hom_tensor_hom_equiv_apply`.
-/
noncomputable
def hom_tensor_hom_equiv : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
rtensor_hom_equiv_hom_rtensor R M P _ ≪≫ₗ
  (linear_equiv.refl R M).arrow_congr (ltensor_hom_equiv_hom_ltensor R N _ Q) ≪≫ₗ
  lift.equiv R M N _

@[simp]
lemma hom_tensor_hom_equiv_to_linear_map :
  (hom_tensor_hom_equiv R M N P Q).to_linear_map = hom_tensor_hom_map R M N P Q :=
begin
  ext f g m n,
  simp only [hom_tensor_hom_equiv, compr₂_apply, mk_apply, linear_equiv.coe_to_linear_map,
  linear_equiv.trans_apply, lift.equiv_apply, linear_equiv.arrow_congr_apply,
  linear_equiv.refl_symm, linear_equiv.refl_apply, rtensor_hom_equiv_hom_rtensor_apply,
  ltensor_hom_equiv_hom_ltensor_apply, ltensor_hom_to_hom_ltensor_apply,
  rtensor_hom_to_hom_rtensor_apply, hom_tensor_hom_map_apply, map_tmul],
end

variables {R M N P Q}

@[simp]
lemma hom_tensor_hom_equiv_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
  hom_tensor_hom_equiv R M N P Q x = hom_tensor_hom_map R M N P Q x :=
by rw [←linear_equiv.coe_to_linear_map, hom_tensor_hom_equiv_to_linear_map]

end comm_ring

end hom_tensor_hom

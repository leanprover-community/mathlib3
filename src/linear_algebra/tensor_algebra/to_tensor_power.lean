/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.tensor_algebra.basic
import linear_algebra.tensor_power
/-!
# Tensor algebras as direct sums of tensor powers

In this file we show that `tensor_algebra R M` is isomorphic to a direct sum of tensor powers, as
`tensor_algebra.equiv_direct_sum`.
-/
open_locale direct_sum tensor_product

variables {R M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]

namespace tensor_power

/-- The canonical embedding from a tensor power to the tensor algebra -/
def to_tensor_algebra {n} : ⨂[R]^n M →ₗ[R] tensor_algebra R M :=
pi_tensor_product.lift (tensor_algebra.tprod R M n)

@[simp]
lemma to_tensor_algebra_tprod {n} (x : fin n → M) :
  tensor_power.to_tensor_algebra (pi_tensor_product.tprod R x) = tensor_algebra.tprod R M n x :=
pi_tensor_product.lift.tprod _

@[simp]
lemma to_tensor_algebra_ghas_one :
  (@graded_monoid.ghas_one.one _ (λ n, ⨂[R]^n M) _ _).to_tensor_algebra = 1 :=
tensor_power.to_tensor_algebra_tprod _

@[simp]
lemma to_tensor_algebra_ghas_mul {i j} (a : ⨂[R]^i M) (b : ⨂[R]^j M) :
  (@graded_monoid.ghas_mul.mul _ (λ n, ⨂[R]^n M) _ _ _ _ a b).to_tensor_algebra
    = a.to_tensor_algebra * b.to_tensor_algebra :=
begin
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [tensor_power.ghas_mul_def, ←linear_map.compr₂_apply, ←@algebra.lmul_apply R,
    ←alg_hom.to_linear_map_apply, ←linear_map.compl₂_apply, ←linear_map.comp_apply],
  refine linear_map.congr_fun (linear_map.congr_fun _ a) b,
  clear a b,
  ext a b,
  simp only [linear_map.compr₂_apply, algebra.lmul_apply, alg_hom.to_linear_map_apply,
    linear_map.compl₂_apply, linear_map.comp_apply, linear_map.comp_multilinear_map_apply,
    pi_tensor_product.lift.tprod, tensor_power.tprod_mul_tprod,
    tensor_power.to_tensor_algebra_tprod, tensor_algebra.tprod_apply],
  refine eq.trans _ list.prod_append,
  congr',
  sorry,  -- a boring statement about `fin` / `list`
end

@[simp]
lemma to_tensor_algebra_galgebra_to_fun (r : R) :
  (@direct_sum.galgebra.to_fun _ R (λ n, ⨂[R]^n M) _ _ _ _ _ _ _ r).to_tensor_algebra
    = _root_.algebra_map _ _ r :=
by rw [tensor_power.galgebra_to_fun_def, tensor_power.algebra_map_eq_smul_one, linear_map.map_smul,
    tensor_power.to_tensor_algebra_ghas_one, algebra.algebra_map_eq_smul_one]

end tensor_power

namespace tensor_algebra

/-- The canonical map from a direct sum of tensor powers to the tensor algebra. -/
def of_direct_sum : (⨁ n, ⨂[R]^n M) →ₐ[R] tensor_algebra R M :=
direct_sum.to_algebra _ _ (λ n, tensor_power.to_tensor_algebra)
  tensor_power.to_tensor_algebra_ghas_one
  (λ i j, tensor_power.to_tensor_algebra_ghas_mul)
  (tensor_power.to_tensor_algebra_galgebra_to_fun)

@[simp] lemma of_direct_sum_of_tprod {n} (x : fin n → M) :
  of_direct_sum (direct_sum.of _ n (pi_tensor_product.tprod R x)) = tprod R M n x :=
(direct_sum.to_add_monoid_of _ _ _).trans (tensor_power.to_tensor_algebra_tprod _)

/-- The canonical map from the tensor algebra to a direct sum of tensor powers. -/
def to_direct_sum : tensor_algebra R M →ₐ[R] ⨁ n, ⨂[R]^n M :=
tensor_algebra.lift R $
  direct_sum.lof R ℕ (λ n, ⨂[R]^n M) _ ∘ₗ
    (linear_equiv.symm $ pi_tensor_product.subsingleton_equiv (0 : fin 1) : M ≃ₗ[R] _).to_linear_map

@[simp] lemma to_direct_sum_ι (x : M) :
  to_direct_sum (ι R x) =
    direct_sum.of (λ n, ⨂[R]^n M) _ (pi_tensor_product.tprod R (λ _ : fin 1, x)) :=
tensor_algebra.lift_ι_apply _ _

lemma of_direct_sum_comp_to_direct_sum :
  of_direct_sum.comp to_direct_sum = alg_hom.id R (tensor_algebra R M) :=
begin
  ext,
  simp [direct_sum.lof_eq_of, tprod_apply],
end

@[simp] lemma of_direct_sum_to_direct_sum (x : tensor_algebra R M):
  of_direct_sum x.to_direct_sum = x :=
alg_hom.congr_fun of_direct_sum_comp_to_direct_sum x

lemma to_direct_sum_tensor_power_tprod {n} (x : fin n → M) :
  to_direct_sum (tprod R M n x) = direct_sum.of _ n (pi_tensor_product.tprod R x) :=
begin
  rw [tprod_apply, alg_hom.map_list_prod, list.map_of_fn, function.comp],
  simp_rw to_direct_sum_ι,
  dsimp only,
  sorry -- something hard about `of` and `list.prod`
end

lemma to_direct_sum_comp_of_direct_sum :
  to_direct_sum.comp of_direct_sum = alg_hom.id R (⨁ n, ⨂[R]^n M) :=
begin
  ext,
  simp [direct_sum.lof_eq_of, -tprod_apply, to_direct_sum_tensor_power_tprod],
end

@[simp] lemma to_direct_sum_of_direct_sum (x : ⨁ n, ⨂[R]^n M):
  (of_direct_sum x).to_direct_sum = x :=
alg_hom.congr_fun to_direct_sum_comp_of_direct_sum x

/-- The tensor algebra is isomorphic to a direct sum of tensor powers -/
@[simps]
def equiv_direct_sum : tensor_algebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M :=
alg_equiv.of_alg_hom to_direct_sum of_direct_sum
  to_direct_sum_comp_of_direct_sum
  of_direct_sum_comp_to_direct_sum

end tensor_algebra

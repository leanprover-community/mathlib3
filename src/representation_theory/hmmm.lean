import representation_theory.tensor_decomp

universes v u

open_locale tensor_product
open tensor_product

section

variables {R : Type*} {A : Type*} {M : Type*} {N : Type*} {P : Type*} [comm_semiring R]
  [semiring A] [algebra R A] [add_comm_monoid M] [module R M] [module A M]
  [is_scalar_tower R A M] [add_comm_monoid N] [module R N] [add_comm_monoid P] [module R P]
  [module A P] [is_scalar_tower R A P] (n : ℕ)

@[simps] def lift_nc (f : M →ₗ[A] (N →ₗ[R] P)) : (M ⊗[R] N) →ₗ[A] P :=
{ map_smul' := λ c, show ∀ x : M ⊗[R] N, (tensor_product.lift (f.restrict_scalars R)).comp
  (algebra.lsmul R _ c) x = (algebra.lsmul R _ c).comp (tensor_product.lift (f.restrict_scalars R)) x,
    from linear_map.ext_iff.1 $ tensor_product.ext' $ λ x y,
    by simp only [linear_map.comp_apply, algebra.lsmul_coe, tensor_product.smul_tmul',
      tensor_product.lift.tmul, linear_map.coe_restrict_scalars_eq_coe,
      f.map_smul, linear_map.smul_apply],
  .. tensor_product.lift (f.restrict_scalars R) }

@[simp] lemma lift_nc_tmul (f : M →ₗ[A] (N →ₗ[R] P)) (x : M) (y : N) :
  lift_nc f (x ⊗ₜ y) = f x y :=
lift.tmul' x y

end

section

variables {k : Type u} (R : Type u) [comm_ring k] [ring R] [algebra k R] {M : Type u} [add_comm_group M]
  [module k M] [module R M] [is_scalar_tower k R M] {ι : Type*} (b : basis ι k M)

noncomputable def to_basis : (R ⊗[k] M) →ₗ[R] (ι →₀ R) :=
lift_nc (linear_map.to_span_singleton R _ ((finsupp.map_range.linear_map
  (linear_map.to_span_singleton k R 1)).comp b.repr.to_linear_map))

lemma to_basis_apply (r : R) (m : M) :
  to_basis R b (r ⊗ₜ m) = r • finsupp.map_range.linear_map (linear_map.to_span_singleton k R 1)
    (b.repr m) :=
begin
  rw [to_basis, lift_nc_tmul],
  refl,
end

lemma to_basis_apply' (r : R) (m : M) (i : ι) :
  to_basis R b (r ⊗ₜ m) i = r * linear_map.to_span_singleton k R 1 (b.repr m i) :=
begin
  rw to_basis_apply,
  refl,
end

noncomputable def of_basis : (ι →₀ R) →ₗ[R] (R ⊗[k] M) :=
finsupp.lift (R ⊗[k] M) R ι (λ i, 1 ⊗ₜ b.repr.symm (finsupp.single i 1))

lemma of_basis_apply (i : ι) (r : R) :
  of_basis R b (finsupp.single i r) = r ⊗ₜ b.repr.symm (finsupp.single i 1) :=
begin
  simp only [of_basis, basis.repr_symm_apply, finsupp.total_single, one_smul, finsupp.lift_apply,
    finsupp.sum_single_index, zero_smul],
  rw [tensor_product.smul_tmul', smul_eq_mul, mul_one]
end

lemma auxd (i : ι) (r : R) :
  to_basis R b (of_basis R b (finsupp.single i r)) = finsupp.single i r :=
begin
  simp [of_basis_apply, to_basis_apply, b.repr.apply_symm_apply],
end

lemma djsk (r : R) (m : M) :
  of_basis R b (to_basis R b (r ⊗ₜ m)) = r ⊗ₜ m :=
begin
  rw [to_basis_apply, linear_map.map_smul, ←finsupp.sum_single (b.repr m),
    linear_map.map_finsupp_sum, linear_map.map_finsupp_sum],
  simp only [finsupp.map_range.linear_map_apply, finsupp.map_range_single, of_basis_apply],
  simp only [linear_map.to_span_singleton_apply, basis.repr_symm_apply, finsupp.total_single, one_smul],
  simp only [tensor_product.smul_tmul],
  unfold finsupp.sum,
  rw [←tmul_sum, smul_tmul', smul_eq_mul, mul_one],
  congr,
  exact b.total_repr _,
end

lemma basis_left_inv (x : R ⊗[k] M) :
  of_basis R b (to_basis R b x) = x :=
begin
  refine x.induction_on _ _ _,
  { simp only [linear_map.map_zero] },
  { intros r m,
    exact djsk _ _ _ _ },
  { intros x y hx hy,
    simp only [map_add, hx, hy] }
end

lemma basis_right_inv (x : ι →₀ R) :
  to_basis R b (of_basis R b x) = x :=
begin
  rw ←x.sum_single,
  simp only [linear_map.map_finsupp_sum, auxd],
end

variables (M)

noncomputable def huh : basis ι R (R ⊗[k] M) :=
{ repr :=
  { inv_fun := of_basis R b,
    left_inv := basis_left_inv R b,
    right_inv := basis_right_inv R b, .. to_basis R b } }

open Rep

#exit
def hmm (G : Type u) [group G] (n : ℕ) : basis (fin n → G) k
  (mul_action_to_Rep k G (fin (n + 1) → G)) :=
basis.map (huh k (mul_action_to_Rep k G (fin n → G)) (linear_equiv.refl _))
(equiv_tensor k G n).symm

end

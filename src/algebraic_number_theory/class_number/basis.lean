import linear_algebra.free_module

lemma submodule.exists_is_basis_of_le_span
  {R : Type*} [integral_domain R] [is_principal_ideal_ring R]
  {M : Type*} [add_comm_group M] [module R M]
  {ι : Type*} [fintype ι] {b : ι → M} (hb : linear_independent R b)
  {N : submodule R M} (le : N ≤ submodule.span R (set.range b)) :
  ∃ (n : ℕ) (b : fin n → N), is_basis R b :=
submodule.exists_is_basis_of_le le (is_basis_span hb)

lemma linear_independent.of_scalar_tower
  {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  {ι : Type*} {b : ι → M} (hb : linear_independent S b)
  (h : function.injective (algebra_map R S)) :
  linear_independent R b :=
begin
  rw linear_independent_iff' at hb ⊢,
  intros s g hg i hi,
  specialize hb s (algebra_map R S ∘ g) _ i hi,
  { exact (algebra_map R S).injective_iff.mp h _ hb },
  simpa using hg
end

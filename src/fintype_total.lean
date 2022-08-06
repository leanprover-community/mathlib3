import linear_algebra.finsupp
section fintype

open_locale big_operators

variables (α M R : Type*) [semiring R] [add_comm_monoid M] [module R M] (v : α → M) [fintype α]

/-- A variant of `finsupp.total` that is defined on fintype indexed vectors. -/
protected def fintype.total : (α → R) →ₗ[R] M :=
{ to_fun := λ f, ∑ i, f i • v i,
  map_add' := λ f g, by { simp_rw [← finset.sum_add_distrib, ← add_smul], refl },
  map_smul' := λ r f, by { simp_rw [finset.smul_sum, smul_smul], refl } }

variables {α M v}

lemma fintype.total_apply (f) : fintype.total α M R v f = ∑ i, f i • v i := rfl

lemma fintype.total_apply_single [decidable_eq α] (i : α) (r : R) :
  fintype.total α M R v (pi.single i r) = r • v i :=
begin
  simp_rw [fintype.total_apply, pi.single_apply, ite_smul, zero_smul],
  rw [finset.sum_ite_eq', if_pos (finset.mem_univ _)]
end

lemma fintype.total_eq_finsupp_total :
  fintype.total α M R v = (finsupp.total α M R v).comp
    (finsupp.linear_equiv_fun_on_fintype R R α).symm.to_linear_map :=
begin
  ext f,
  symmetry,
  apply finset.sum_subset,
  { exact finset.subset_univ _ },
  { intros x _ hx,
    rw finsupp.not_mem_support_iff.mp hx,
    exact zero_smul _ _ }
end

lemma fintype.range_total : (fintype.total α M R v).range = submodule.span R (set.range v) :=
by rw [fintype.total_eq_finsupp_total, linear_map.range_comp,
  linear_equiv.to_linear_map_eq_coe, linear_equiv.range, submodule.map_top, finsupp.range_total]

end fintype

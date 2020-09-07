import ring_theory.witt_vector.witt_vector_preps

open_locale big_operators

namespace mv_polynomial
variables {σ τ R S : Type*} [comm_ring R] [comm_ring S]

-- give this a better name
def nice {σ τ : Type*} (φ : mv_polynomial (σ × τ) R) : Prop :=
∀ ⦃d⦄, φ.coeff d ≠ 0 → ∀ i : σ, ∃ j : τ, (i, j) ∈ d.support

namespace nice

lemma add {φ ψ : mv_polynomial (σ × τ) R} (hφ : φ.nice) (hψ : ψ.nice) :
  (φ + ψ).nice :=
begin
  intros d hd,
  rw coeff_add at hd,
  by_cases H : φ.coeff d = 0,
  { rw [H, zero_add] at hd,
    exact hψ hd },
  { exact hφ H },
end

lemma zero : (0 : mv_polynomial (σ × τ) R).nice :=
by { intro, rw coeff_zero, intro, contradiction }

lemma sum {ι : Type*} (f : ι → mv_polynomial (σ × τ) R) (s : finset ι) (hf : ∀ i ∈ s, (f i).nice) :
  (∑ i in s, f i).nice :=
begin
  classical,
  revert hf,
  apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
      not_false_iff, forall_true_iff],
    exact zero },
  { intros i s his IH h,
    rw finset.sum_insert his,
    apply add,
    { exact h i (finset.mem_insert_self i s), },
    { apply IH,
      intros j hjs,
      exact h j (finset.mem_insert_of_mem hjs) } }
end

lemma nice_mul {φ : mv_polynomial (σ × τ) R} (hφ : φ.nice) (ψ : mv_polynomial (σ × τ) R) :
  (φ * ψ).nice :=
begin
  apply induction_on ψ,
  { intros r d hd i,
    rw [mul_comm, coeff_C_mul] at hd,
    apply hφ _ i,
    contrapose! hd,
    rw [hd, mul_zero] },
  { intros, rw [mul_add], apply add; assumption },
  { rintro ψ' k ih d hd i,
    rw [← mul_assoc, coeff_mul_X'] at hd,
    split_ifs at hd with hk, swap, contradiction,
    obtain ⟨j, hj⟩ := ih hd i,
    refine ⟨j, _⟩,
    rw [finsupp.mem_support_iff, ← nat.pos_iff_ne_zero] at hj ⊢,
    rw [finsupp.nat_sub_apply] at hj,
    exact lt_of_lt_of_le hj (nat.sub_le_self _ _), }
end

lemma mul_nice (φ : mv_polynomial (σ × τ) R) {ψ : mv_polynomial (σ × τ) R} (hψ : ψ.nice) :
  (φ * ψ).nice :=
begin
  apply induction_on φ,
  { intros r d hd i,
    rw [coeff_C_mul] at hd,
    apply hψ _ i,
    contrapose! hd,
    rw [hd, mul_zero] },
  { intros, rw [add_mul], apply add; assumption },
  { rintro ψ' k ih d hd i,
    rw [mul_right_comm, coeff_mul_X'] at hd,
    split_ifs at hd with hk, swap, contradiction,
    obtain ⟨j, hj⟩ := ih hd i,
    refine ⟨j, _⟩,
    rw [finsupp.mem_support_iff, ← nat.pos_iff_ne_zero] at hj ⊢,
    rw [finsupp.nat_sub_apply] at hj,
    exact lt_of_lt_of_le hj (nat.sub_le_self _ _), }
end

lemma prod {ι : Type*} (f : ι → mv_polynomial (σ × τ) R) (s : finset ι) (hf : ∃ i ∈ s, (f i).nice) :
  (∏ i in s, f i).nice :=
begin
  classical,
  obtain ⟨i, his, hi⟩ := hf,
  rw [← finset.insert_erase his, finset.prod_insert (finset.not_mem_erase i s)],
  apply hi.nice_mul,
end

lemma pow {φ : mv_polynomial (σ × τ) R} (hφ : φ.nice) (n : ℕ) (hn : n ≠ 0) :
  (φ ^ n).nice :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn,
  rw pow_succ,
  apply hφ.nice_mul
end

lemma of_map_of_injective (f : R →+* S) (hf : function.injective f) (φ : mv_polynomial (σ × τ) R)
  (h : (map f φ).nice) :
  φ.nice :=
begin
  intros d hd i,
  apply h,
  rw coeff_map,
  contrapose! hd,
  apply hf,
  rwa f.map_zero
end

lemma bind₁_left {ι : Type*} (f : ι → mv_polynomial (σ × τ) R) (hf : ∀ i, (f i).nice)
  (φ : mv_polynomial ι R) (hφ : constant_coeff φ = 0) :
  (bind₁ f φ).nice :=
begin
  rw φ.as_sum,
  simp only [coeff_sum, alg_hom.map_sum, bind₁_monomial, coeff_C_mul],
  apply sum,
  intros d hd,
  apply mul_nice,
  rw [constant_coeff_eq, coeff, ← finsupp.not_mem_support_iff] at hφ,
  obtain ⟨i, hi⟩ : d.support.nonempty,
  { rw [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty],
    rintro rfl, contradiction },
  apply prod,
  refine ⟨i, hi, _⟩,
  apply (hf i).pow,
  rwa finsupp.mem_support_iff at hi,
end

lemma bind₁_right {ι : Type*} (f : ι → mv_polynomial (σ × τ) R) (hf : ∀ i, (f i).nice)
  (φ : mv_polynomial ι R) (hφ : constant_coeff φ = 0) :
  (bind₁ f φ).nice :=
begin
  rw φ.as_sum,
  simp only [coeff_sum, alg_hom.map_sum, bind₁_monomial, coeff_C_mul],
  apply sum,
  intros d hd,
  apply mul_nice,
  rw [constant_coeff_eq, coeff, ← finsupp.not_mem_support_iff] at hφ,
  obtain ⟨i, hi⟩ : d.support.nonempty,
  { rw [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty],
    rintro rfl, contradiction },
  apply prod,
  refine ⟨i, hi, _⟩,
  apply (hf i).pow,
  rwa finsupp.mem_support_iff at hi,
end

end nice



end mv_polynomial

import ring_theory.class_number.absolute_value
import linear_algebra.determinant

open_locale big_operators

section det

open equiv finset matrix

variables {R S : Type*} [comm_ring R] [nontrivial R] [linear_ordered_comm_ring S]
variables {n : Type*} [fintype n] [decidable_eq n]

-- 3.4: a bound on the determinant
lemma det_le {A : matrix n n R} {f : absolute_value R S}
  {x : S} (hx : ∀ i j, f (A i j) ≤ x) :
  f A.det ≤ nat.factorial (fintype.card n) • x ^ (fintype.card n) :=
calc f A.det ≤ ∑ σ : perm n, f ((σ.sign : ℤ) * ∏ i, A (σ i) i) : f.le_sum _ _
         ... = ∑ σ : perm n, (∏ i, f (A (σ i) i)) : sum_congr rfl (λ σ hσ,
           by rw [f.map_mul, f.map_units, one_mul, f.map_prod])
         ... ≤ ∑ σ : perm n, (∏ (i : n), x) :
           sum_le_sum (λ _ _, prod_le_prod (λ _ _, f.nonneg _) (λ _ _, hx _ _))
         ... = ∑ σ : perm n, x ^ (fintype.card n) : sum_congr rfl (λ _ _,
           by rw [prod_const, finset.card_univ])
         ... = nat.factorial (fintype.card n) •ℕ x ^ (fintype.card n) :
           by rw [sum_const, finset.card_univ, fintype.card_perm]

lemma det_sum_le {ι : Type*} (s : finset ι) {c : ι → R} {A : ι → matrix n n R}
  {f : absolute_value R S}
  {x : S} (hx : ∀ k i j, f (A k i j) ≤ x) {y : S} (hy : ∀ k, f (c k) ≤ y) :
  f (det (∑ k in s, c k • A k)) ≤ nat.factorial (fintype.card n) • (finset.card s • (x * y)) ^ (fintype.card n) :=
begin
  have : ∀ i j, f ((∑ k in s, (c k • A k)) i j) ≤ finset.card s • (x * y),
  { intros i j,
    calc f ((∑ k in s, (c k • A k)) i j)
        = f (∑ k in s, (c k • A k) i j) : by simp only [sum_apply]
    ... ≤ ∑ k in s, f ((c k • A k) i j) : f.le_sum _ _
    ... = ∑ k in s, f (A k i j) * f (c k) : sum_congr rfl (λ k _,
      by rw [matrix.smul_apply, mul_comm, f.map_mul])
    ... ≤ ∑ k in s, x * y : sum_le_sum (λ k _, mul_le_mul (hx _ _ _) (hy _)
      (f.nonneg _) (le_trans (f.nonneg _) (hx k i j)))
    ... = s.card •ℕ (x * y) : sum_const _, },
  exact det_le this
end

end det

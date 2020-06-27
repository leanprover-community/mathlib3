import data.polynomial

open polynomial
open finset
open_locale big_operators

-- TODO everything here should move up to cayley_hamilton.lean or down to polynomial.lean/...


variables {R S : Type*}

section ring
variables [ring R]

variables [ring S]
variables (f : R → S) (x : S)
variables [is_ring_hom f]

lemma foo {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - monomial 0 r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
sorry

-- @[simp] lemma quux {p : polynomial R} : p.coeff (p.nat_degree + 1) = 0 := sorry

lemma sum_over_range' (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
  (n : ℕ) (w : p.nat_degree < n) :
  p.sum f = ∑ (a : ℕ) in range n, f a (coeff p a) :=
begin
  rw finsupp.sum,
  apply finset.sum_bij_ne_zero (λ n _ _, n),
  { intros k h₁ h₂, simp only [mem_range],
    calc k ≤ p.nat_degree : _
       ... < n : w,
    rw finsupp.mem_support_iff at h₁,
    exact le_nat_degree_of_ne_zero h₁, },
  { intros, assumption },
  { intros b hb hb',
    refine ⟨b, _, hb', rfl⟩,
    rw finsupp.mem_support_iff,
    contrapose! hb',
    convert h b, },
  { intros, refl }
end

lemma sum_over_range (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)

@[simp] lemma coeff_monomial (n : ℕ) (r : R) : coeff (monomial n r) n = r :=
by rw [monomial_eq_smul_X, coeff_smul, coeff_X_pow, if_pos rfl, mul_one]

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
begin
  apply polynomial.induction_on' p,
  { intros φ ψ hφ hψ, rw [add_mul, coeff_add, coeff_add, add_mul, hφ, hψ], },
  intros m r,
  apply polynomial.induction_on' q,
  { intros φ ψ hφ hψ, rw [mul_add, coeff_add, coeff_add, mul_add, hφ, hψ], },
  intros n s,
  rw [monomial_eq_smul_X, monomial_eq_smul_X, ← C_mul', ← C_mul', X_pow_mul_assoc, ← mul_assoc,
      ← C_mul, mul_assoc, ← pow_add, coeff_C_mul, coeff_C_mul, coeff_C_mul],
  simp only [if_t_t, mul_boole, coeff_X_pow, zero_mul, ite_mul, mul_ite, mul_zero],
  cases n,
  { simp only [mul_one, nat.nat_zero_eq_zero, if_true, eq_self_iff_true, zero_add],
    split_ifs; refl },
  cases m,
  { simp only [mul_one, if_true, eq_self_iff_true], },
  rw [if_neg, if_neg],
  { exact (nat.succ_ne_zero n).symm },
  { simp only [nat.succ_eq_add_one, ←add_assoc], exact (nat.succ_ne_zero _).symm }
end

lemma eval₂_mul_X_sub_monomial {p : polynomial R} {r : R} :
  (p * (X - monomial 0 r)).eval₂ f (f r) = 0 :=
begin
  simp [eval₂],
  rw sum_over_range' _ _ (p.nat_degree + 2) sorry,
  swap,
  { simp [is_ring_hom.map_zero f], },
  rw sum_range_succ',
  conv_lhs {
    congr,
    apply_congr,
    skip,
    rw [foo],
    rw [is_ring_hom.map_sub f],
    rw [is_ring_hom.map_mul f],
    rw [sub_mul],
    rw [mul_assoc, ←pow_succ],
  },
  conv_lhs {
    congr,
    skip,
    simp [coeff_sub],
    rw [is_ring_hom.map_neg f],
    rw [is_ring_hom.map_mul f],
  },
  rw sum_range_sub',
  simp [is_ring_hom.map_zero f],
end

lemma eval₂_mul_X_sub_monomial' {p : polynomial R} (r : R) :
  (p * (X - monomial 0 r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial id

lemma eval₂_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial id

end ring

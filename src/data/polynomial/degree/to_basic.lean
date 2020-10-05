import data.polynomial.degree.basic

open polynomial finsupp finset

variables {R : Type*} [semiring R] {f : polynomial R}

--Put this next to degree_monomial, and maybe use that lemma for a shorter proof?
@[simp] lemma nat_degree_monomial {a : R} (n : ℕ) (ha : a ≠ 0) : nat_degree (C a * X ^ n) = n :=
nat_degree_eq_of_degree_eq_some (degree_monomial n ha)

lemma mem_support_C_mul_X_pow {n a : ℕ} {c : R} : a ∈ (C c * X ^ n).support → a = n :=
begin
  rw [mem_support_iff_coeff_ne_zero, coeff_C_mul_X c n a],
  split_ifs,
    { intro,
      assumption, },
    { intro a_1,
    exfalso,
    apply a_1,
    refl, },
end

lemma support_C_mul_X_pow (c : R) (n : ℕ) : (C c * X ^ n).support ⊆ singleton n :=
begin
  intro a,
  rw mem_singleton,
  exact mem_support_C_mul_X_pow,
end

lemma card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : (C c * X ^ n).support.card ≤ 1 :=
begin
  rw ← card_singleton n,
  apply card_le_of_subset (support_C_mul_X_pow c n),
end

lemma nat_degree_mem_support_of_nonzero (H : f ≠ 0) : f.nat_degree ∈ f.support :=
(f.mem_support_to_fun f.nat_degree).mpr ((not_congr leading_coeff_eq_zero).mpr H)

lemma le_nat_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → a ≤ nat_degree f:=
le_nat_degree_of_ne_zero ∘ mem_support_iff_coeff_ne_zero.mp

lemma le_degree_of_mem_supp (a : ℕ) :
  a ∈ f.support → ↑a ≤ degree f :=
le_degree_of_ne_zero ∘ mem_support_iff_coeff_ne_zero.mp

lemma nonempty_support_iff : f.support.nonempty ↔ f ≠ 0 :=
begin
  rw [ne.def, nonempty_iff_ne_empty, ne.def, ← support_eq_empty],
end

lemma nat_degree_eq_support_max' (h : f ≠ 0) :
  f.nat_degree = f.support.max' (nonempty_support_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply finset.le_max',
    rw mem_support_iff_coeff_ne_zero,
    exact (not_congr leading_coeff_eq_zero).mpr h, },
  { apply max'_le,
    refine le_nat_degree_of_mem_supp, },
end

lemma support_C_mul_X_pow_nonzero {c : R} {n : ℕ} (h : c ≠ 0): (C c * X ^ n).support = singleton n :=
begin
  ext1,
  rw [mem_singleton],
  split,
    { exact mem_support_C_mul_X_pow, },
    { intro,
      rwa [mem_support_iff_coeff_ne_zero, ne.def, a_1, coeff_C_mul, coeff_X_pow_self n, mul_one], },
end

lemma nat_degree_C_mul_X_pow_le (a : R) (n : ℕ) : nat_degree (C a * X ^ n) ≤ n :=
begin
  by_cases a0 : a = 0,
    { rw [a0, C_0, zero_mul, nat_degree_zero],
      exact nat.zero_le _, },
    { rw nat_degree_eq_support_max',
      { simp_rw [support_C_mul_X_pow_nonzero a0, max'_singleton n], },
      { intro,
        apply a0,
        rw [← C_inj, C_0],
        apply mul_X_pow_eq_zero a_1, }, },
end


lemma nat_degree_C_mul_X_pow_nonzero {a : R} (n : ℕ) (ha : a ≠ 0) : nat_degree (C a * X ^ n) = n :=
begin
  rw nat_degree_eq_support_max',
    { simp_rw [support_C_mul_X_pow_nonzero ha, max'_singleton n], },
    { intro,
      apply ha,
      rw [← C_inj, C_0],
      exact mul_X_pow_eq_zero a_1, },
end

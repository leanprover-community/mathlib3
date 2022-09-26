import ring_theory.polynomial.cyclotomic.eval

noncomputable theory

open_locale big_operators

section cyclotomic₂

open polynomial

def cyclotomic₂ (n : ℕ) (R : Type*) [ring R] [has_div R] : R → R → R :=
λ a b, b ^ (nat.totient n) * (polynomial.cyclotomic n R).eval (a / b)

lemma cyclotomic₂_div_prod_eq (n : ℕ) (R : Type*) [field R] (a b : R) (hn : 0 < n)
  (hbne: b ≠ 0) : ∏ d in nat.divisors n, cyclotomic₂ d R a b = a ^ n - b ^ n :=
begin
  simp_rw [cyclotomic₂, finset.prod_mul_distrib, ← eval_prod, prod_cyclotomic_eq_X_pow_sub_one hn,
   finset.prod_pow_eq_pow_sum, nat.sum_totient, eval_sub, eval_pow, eval_X, eval_one],
  field_simp [hbne, mul_comm]
end

lemma transport (n : ℕ) (R S : Type*) [ring R] [ring S] [has_div R] [division_monoid S] (f : R →+* S)
  (a b : R) :
  f (cyclotomic₂ n R a b) = cyclotomic₂ n S (f a) (f b) :=
begin
  haveI temp : monoid_hom_class (R →+* S) R S := by apply_instance,
  haveI groupR: group R := multiplicative.group,
  simp only [cyclotomic₂],
  simp,
  rw ← cyclotomic.eval_apply (a / b) n _,
  sorry
end

lemma proposition_1 (n p : ℕ) (R : Type*) [field R] (a b : R)
  (hp: nat.prime p) (hpn: p ∣ n) :
  cyclotomic₂ (n * p) R a b = cyclotomic₂ n R (a ^ p) (b ^ p) :=
by simp_rw [cyclotomic₂, ← cyclotomic_expand_eq_cyclotomic hp hpn, expand_eval, div_pow,
   mul_comm n p, nat.totient_mul_of_prime_of_dvd hp hpn, pow_mul]

lemma proposition_2 (n p : ℕ) (R : Type*) [field R] (a b : R)
  (hp: nat.prime p) (hpn: ¬ p ∣ n) :
  cyclotomic₂ (n * p) R a b * cyclotomic₂ n R a b = cyclotomic₂ n R (a ^ p) (b ^ p) :=
calc
  cyclotomic₂ (n * p) R a b * cyclotomic₂ n R a b =
    b ^ (nat.totient (n * p) + nat.totient n) * (expand R p (cyclotomic n R)).eval (a / b) :
  by { simp only [cyclotomic₂, cyclotomic_expand_eq_cyclotomic_mul hp hpn, eval_mul]; ring_exp_eq }
  ... = cyclotomic₂ n R (a ^ p) (b ^ p) : by { simp only [cyclotomic₂, expand_eval, div_pow,
   mul_comm n p, nat.totient_mul_of_prime_of_not_dvd hp hpn, ← pow_mul, mul_eq_mul_right_iff],
  left, conv_rhs {rw [← nat.sub_add_cancel (show 1 ≤ p, by linarith [nat.prime.two_le hp])]},
  ring_nf }

lemma proposition_3 (n : ℕ) (a b : ℝ) (hn : 2 ≤ n) (hab : b < a) (hb : 0 < b) :
  (a - b) ^ (nat.totient n) < cyclotomic₂ n ℝ a b :=
calc
  (a - b) ^ (nat.totient n) =  b ^ n.totient * (a / b - 1) ^ n.totient :
    by simp only [← mul_pow, mul_sub, mul_one, mul_div_cancel' a (ne_of_gt hb)]
  ... < cyclotomic₂ n ℝ a b : by simp only [cyclotomic₂, mul_lt_mul_left (pow_pos hb n.totient),
   sub_one_pow_totient_lt_cyclotomic_eval hn (show 1 < a / b, by simpa [one_lt_div hb])]

lemma proposition_4 (n : ℕ) (a b : ℝ) (hn : 3 ≤ n) (hab : b < a) (hb : 0 < b) :
  cyclotomic₂ n ℝ a b < (a + b) ^ (nat.totient n) :=
calc
  cyclotomic₂ n ℝ a b < b ^ (nat.totient n) * (a / b + 1) ^ (nat.totient n) :
    by simp only [cyclotomic₂, mul_lt_mul_left (pow_pos hb n.totient),
    cyclotomic_eval_lt_sub_one_pow_totient hn (show 1 < a / b, by simpa [one_lt_div hb])]
  ... = (a + b) ^ (nat.totient n) : by simp only [← mul_pow, mul_add, mul_one,
    mul_div_cancel' a (ne_of_gt hb)]

lemma proposition_4_aux (n : ℕ) (a b : ℚ) (hn : 3 ≤ n) (hab : b < a) (hb : 0 < b) :
  cyclotomic₂ n ℚ a b < (a + b) ^ (nat.totient n) :=
begin
  sorry
end

lemma proposition_5 (n : ℕ) (a b : ℤ) :
  ∃ k : ℤ, cyclotomic₂ n ℂ a b = k :=
begin
  rcases eq_or_ne n 0 with rfl | hzero,
  { use 1, simp only [cyclotomic₂, cyclotomic_zero, nat.totient_zero, pow_zero, eval_one,
     mul_one, int.cast_one]},
  rcases eq_or_ne b 0 with rfl | hbzero,
  { refine ⟨0, by norm_num [cyclotomic₂, nat.totient_pos (nat.pos_of_ne_zero hzero)]⟩ },
  { replace hbzero : (b : ℂ) ≠ 0, by simp only [ne.def, int.cast_eq_zero, hbzero, not_false_iff],
    rw cyclotomic₂,
    rw ← map_cyclotomic_int n ℂ,
    simp_rw eval_map,
    rw eval₂_eq_sum_range,
    simp,
    simp_rw nat_degree_cyclotomic,
    rw finset.mul_sum,
    have : ∀ x ∈ finset.range (n.totient + 1),
     (b : ℂ) ^ n.totient * (↑((cyclotomic n ℤ).coeff x) * (↑a ^ x / ↑b ^ x)) =
     ↑(((cyclotomic n ℤ).coeff x) * (a ^ x * b ^ (n.totient - x))),
    { intros x hx,
      rw finset.mem_range_succ_iff at hx,
      calc
      (b : ℂ) ^ n.totient * (↑((cyclotomic n ℤ).coeff x) * (↑a ^ x / ↑b ^ x)) =
        ↑((cyclotomic n ℤ).coeff x) * ↑a ^ x * (↑b ^ n.totient * (↑b ^ x)⁻¹)  : by { ring_exp }
      ... = ↑(((cyclotomic n ℤ).coeff x) * (a ^ x * b ^ (n.totient - x))) :
        by { simp only [←pow_sub₀ (b : ℂ) hbzero hx, ←mul_assoc,
          int.cast_mul, int.cast_pow] }},
    simp only [finset.sum_congr rfl this, ← int.cast_sum, int.cast_inj, exists_eq']}
end

end cyclotomic₂

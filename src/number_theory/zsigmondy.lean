import ring_theory.polynomial.cyclotomic.eval

noncomputable theory

open_locale big_operators

section cyclotomic₂

open polynomial

def cyclotomic₂' (n : ℕ) (R : Type*) [ring R] [has_div R] : R → R → R :=
λ a b, b ^ (nat.totient n) * (polynomial.cyclotomic n R).eval (a / b)

lemma cyclotomic₂'_div_prod_eq {n : ℕ} (R : Type*) [field R] (a b : R) (hn : 0 < n)
  (hbne: b ≠ 0) : ∏ d in nat.divisors n, cyclotomic₂' d R a b = a ^ n - b ^ n :=
begin
  simp_rw [cyclotomic₂', finset.prod_mul_distrib, ← eval_prod, prod_cyclotomic_eq_X_pow_sub_one hn,
   finset.prod_pow_eq_pow_sum, nat.sum_totient, eval_sub, eval_pow, eval_X, eval_one],
  field_simp [hbne, mul_comm]
end

lemma cyclotomic₂'_apply (n : ℕ) {R S : Type*} [field R] [field S] (f : R →+* S) (a b : R) :
  f (cyclotomic₂' n R a b) = cyclotomic₂' n S (f a) (f b) :=
by simp only [cyclotomic₂', ←cyclotomic.eval_apply (a / b), map_div₀ f a b, map_mul, map_pow]

lemma proposition_1 {n p : ℕ} (R : Type*) [field R] (a b : R)
  (hp: nat.prime p) (hpn: p ∣ n) :
  cyclotomic₂' (n * p) R a b = cyclotomic₂' n R (a ^ p) (b ^ p) :=
by simp_rw [cyclotomic₂', ← cyclotomic_expand_eq_cyclotomic hp hpn, expand_eval, div_pow,
   mul_comm n p, nat.totient_mul_of_prime_of_dvd hp hpn, pow_mul]

lemma proposition_2 {n p : ℕ} (R : Type*) [field R] (a b : R)
  (hp: nat.prime p) (hpn: ¬ p ∣ n) :
  cyclotomic₂' (n * p) R a b * cyclotomic₂' n R a b = cyclotomic₂' n R (a ^ p) (b ^ p) :=
calc
  cyclotomic₂' (n * p) R a b * cyclotomic₂' n R a b =
    b ^ (nat.totient (n * p) + nat.totient n) * (expand R p (cyclotomic n R)).eval (a / b) :
  by { simp only [cyclotomic₂', cyclotomic_expand_eq_cyclotomic_mul hp hpn, eval_mul]; ring_exp_eq }
  ... = cyclotomic₂' n R (a ^ p) (b ^ p) : by { simp only [cyclotomic₂', expand_eval, div_pow,
   mul_comm n p, nat.totient_mul_of_prime_of_not_dvd hp hpn, ← pow_mul, mul_eq_mul_right_iff],
  left, conv_rhs {rw [← nat.sub_add_cancel (show 1 ≤ p, by linarith [nat.prime.two_le hp])]},
  ring_nf }

lemma proposition_3 {n : ℕ} {a b : ℝ} (hn : 2 ≤ n) (hab : b < a) (hb : 0 < b) :
  (a - b) ^ (nat.totient n) < cyclotomic₂' n ℝ a b :=
calc
  (a - b) ^ (nat.totient n) =  b ^ n.totient * (a / b - 1) ^ n.totient :
    by simp only [← mul_pow, mul_sub, mul_one, mul_div_cancel' a (ne_of_gt hb)]
  ... < cyclotomic₂' n ℝ a b : by simp only [cyclotomic₂', mul_lt_mul_left (pow_pos hb n.totient),
   sub_one_pow_totient_lt_cyclotomic_eval hn (show 1 < a / b, by simpa [one_lt_div hb])]

lemma proposition_4 {n : ℕ} {a b : ℝ} (hn : 3 ≤ n) (hab : b < a) (hb : 0 < b) :
  cyclotomic₂' n ℝ a b < (a + b) ^ (nat.totient n) :=
calc
  cyclotomic₂' n ℝ a b < b ^ (nat.totient n) * (a / b + 1) ^ (nat.totient n) :
    by simp only [cyclotomic₂', mul_lt_mul_left (pow_pos hb n.totient),
    cyclotomic_eval_lt_sub_one_pow_totient hn (show 1 < a / b, by simpa [one_lt_div hb])]
  ... = (a + b) ^ (nat.totient n) : by simp only [← mul_pow, mul_add, mul_one,
    mul_div_cancel' a (ne_of_gt hb)]

lemma proposition_5 (n : ℕ) (a b : ℤ) :
  ∃ k : ℤ, cyclotomic₂' n ℂ a b = k :=
begin
  rcases eq_or_ne n 0 with rfl | hzero,
  { refine ⟨1, by simp only [cyclotomic₂', cyclotomic_zero, nat.totient_zero, pow_zero, eval_one,
     mul_one, int.cast_one]⟩},
  rcases eq_or_ne b 0 with rfl | hbzero,
  { refine ⟨0, by norm_num [cyclotomic₂', nat.totient_pos (nat.pos_of_ne_zero hzero)]⟩ },
  { replace hbzero : (b : ℂ) ≠ 0, by simp only [ne.def, int.cast_eq_zero, hbzero, not_false_iff],
    simp only [cyclotomic₂', ← map_cyclotomic_int n ℂ, eval_map, eval₂_eq_sum_range, eq_int_cast,
     div_pow, nat_degree_cyclotomic, finset.mul_sum],
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

def cyclotomic₂ (n : ℕ) : ℤ → ℤ → ℤ :=
λ a b, classical.some (proposition_5 n a b)

lemma cyclotomic₂_def (n : ℕ) (a b : ℤ) :
  cyclotomic₂' n ℂ a b = cyclotomic₂ n a b :=
by { rw [cyclotomic₂]; exact classical.some_spec (proposition_5 n a b) }

lemma cyclotomic₂_def' (n : ℕ) (a b : ℤ) :
  cyclotomic₂' n ℝ a b = cyclotomic₂ n a b :=
begin
  have := cyclotomic₂'_apply n (algebra_map ℝ ℂ) a b,
  simp only [complex.coe_algebra_map, complex.of_real_int_cast] at this,
  simp only [←complex.of_real_inj, this, cyclotomic₂_def n a b, complex.of_real_int_cast],
end

lemma proposition_6 {n : ℕ} {a b : ℤ} (hn : 2 ≤ n) (hab : b < a) (hb : 0 < b) :
  (a - b) ^ (nat.totient n) < cyclotomic₂ n a b :=
by simp only [← @int.cast_lt ℝ, ← cyclotomic₂_def', int.cast_pow, int.cast_sub,
    proposition_3 hn (int.cast_lt.mpr hab) (show (0 : ℝ) < b, by simp only [int.cast_pos, hb])]

lemma proposition_7 {n : ℕ} {a b : ℤ} (hn : 3 ≤ n) (hab : b < a) (hb : 0 < b) :
  cyclotomic₂ n a b < (a + b) ^ (nat.totient n) :=
by simp only [← @int.cast_lt ℝ, ← cyclotomic₂_def', int.cast_pow, int.cast_add,
    proposition_4 hn (int.cast_lt.mpr hab) (show (0 : ℝ) < b, by simp only [int.cast_pos, hb])]

lemma cyclotomic₂_div_prod_eq {n : ℕ} (a b : ℤ) (hn : 0 < n) (hbne: b ≠ 0) :
  ∏ d in nat.divisors n, cyclotomic₂ d a b = a ^ n - b ^ n :=
by simp only [← @int.cast_inj ℝ, int.cast_prod, int.cast_sub, int.cast_pow, ← cyclotomic₂_def',
    cyclotomic₂'_div_prod_eq ℝ ↑a ↑b hn (show (b : ℝ) ≠ 0, by norm_num [hbne])]

lemma proposition_8 {n p : ℕ} (a b : ℤ) (hp: nat.prime p) (hpn: p ∣ n) :
  cyclotomic₂ (n * p) a b = cyclotomic₂ n (a ^ p) (b ^ p) :=
by simp only [← @int.cast_inj ℝ, ← cyclotomic₂_def', int.cast_pow, proposition_1 ℝ ↑a ↑b hp hpn]

lemma proposition_9 {n p : ℕ} (a b : ℤ) (hp: nat.prime p) (hpn: ¬ p ∣ n) :
  cyclotomic₂ (n * p) a b * cyclotomic₂ n a b = cyclotomic₂ n (a ^ p) (b ^ p) :=
by simp only [← @int.cast_inj ℝ, ← cyclotomic₂_def', int.cast_pow, int.cast_mul,
  proposition_2 ℝ ↑a ↑b hp hpn]

end cyclotomic₂

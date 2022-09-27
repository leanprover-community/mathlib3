import ring_theory.polynomial.cyclotomic.eval

noncomputable theory

open_locale big_operators

section cyclotomic₂

open polynomial

def cyclotomic₂' (n : ℕ) (R : Type*) [ring R] [has_div R] : R → R → R :=
λ a b, b ^ (nat.totient n) * (polynomial.cyclotomic n R).eval (a / b)

@[simp] lemma cyclotomic₂'_zero (R : Type*) [ring R] [has_div R] (a b : R) :
  cyclotomic₂' 0 R a b = 1 :=
by simp only [cyclotomic₂', nat.totient_zero, pow_zero, cyclotomic_zero, eval_one, mul_one]

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

lemma cyclotomic₂_def_int (n : ℕ) (a b : ℤ) :
  cyclotomic₂' n ℤ a b = cyclotomic₂ n a b :=
begin
  sorry
end

@[simp] lemma cyclotomic₂_zero (a b : ℤ) : cyclotomic₂ 0 a b = 1 :=
  by simp only [←(@ int.cast_inj) ℝ, ←cyclotomic₂_def', cyclotomic₂'_zero, int.cast_one]

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

lemma cyclotomic₂_dvd_pow_sub (n : ℕ) (a b : ℤ) (hb : b ≠ 0):
  cyclotomic₂ n a b ∣ a ^ n - b ^ n :=
begin
  rcases nat.eq_zero_or_pos n with rfl | hnzero,
  { simp only [cyclotomic₂_zero, is_unit.dvd, is_unit_one] },
  { simp only [← cyclotomic₂_div_prod_eq a b hnzero hb,
    nat.divisors_eq_proper_divisors_insert_self_of_pos hnzero,
    finset.prod_insert (@nat.proper_divisors.not_self_mem n), dvd_mul_right] }
end

lemma proposition_8 {n p : ℕ} (a b : ℤ) (hp: nat.prime p) (hpn: p ∣ n) :
  cyclotomic₂ (n * p) a b = cyclotomic₂ n (a ^ p) (b ^ p) :=
by simp only [← @int.cast_inj ℝ, ← cyclotomic₂_def', int.cast_pow, proposition_1 ℝ ↑a ↑b hp hpn]

lemma proposition_9 {n p : ℕ} (a b : ℤ) (hp: nat.prime p) (hpn: ¬ p ∣ n) :
  cyclotomic₂ (n * p) a b * cyclotomic₂ n a b = cyclotomic₂ n (a ^ p) (b ^ p) :=
by simp only [← @int.cast_inj ℝ, ← cyclotomic₂_def', int.cast_pow, int.cast_mul,
  proposition_2 ℝ ↑a ↑b hp hpn]

lemma prime_div_pow_sub {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ (p - 1) - b ^ (p - 1) :=
by exact int.modeq.dvd (int.modeq.trans (int.modeq.pow_card_sub_one_eq_one hp
    ((prime.coprime_iff_not_dvd (nat.prime_iff_prime_int.mp hp)).mpr hpb).symm)
    ((int.modeq.pow_card_sub_one_eq_one hp ((prime.coprime_iff_not_dvd
    (nat.prime_iff_prime_int.mp hp)).mpr hpa).symm)).symm)

def least_div_pow {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :=
  nat.find (show ∃ k : ℕ, ↑p ∣ a ^ k - b ^ k ∧ 0 < k,
    by refine ⟨p -1, (prime_div_pow_sub hp hpa hpb), by norm_num [nat.prime.one_lt hp]⟩)

lemma least_div_pow_pos {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  0 < least_div_pow hp hpa hpb :=
  by simp only [least_div_pow, nat.find_pos, nat.not_lt_zero,
  and_false, not_false_iff]

lemma least_div_pow_min {p k : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b)
  (hk : 0 < k) :
  k < least_div_pow hp hpa hpb → ¬ ↑p ∣ a ^ k - b ^ k :=
begin
 rw [least_div_pow],
 intro h,
 have := nat.find_min _ h,
 simpa [not_and, not_lt, le_zero_iff, ne_of_gt hk]
end

lemma least_div_pow_dvd {p n : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ n - b ^ n → least_div_pow hp hpa hpb ∣ n :=
begin
  rcases nat.eq_zero_or_pos n with rfl | hzero,
  { simp only [pow_zero, sub_self, dvd_zero, forall_true_left] },
  { sorry },
end

lemma proposition_10 {p : ℕ} {a b : ℤ} (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) (hpge: 3 ≤ p)
  (hp : nat.prime p) :
  multiplicity ↑p (cyclotomic₂ (least_div_pow hp hpa hpb) a b) =
  multiplicity ↑p (a ^ (least_div_pow hp hpa hpb) - b ^ (least_div_pow hp hpa hpb)) :=
begin
  have hbne : b ≠ 0,
  { rintro rfl; simp only [dvd_zero, not_true] at hpb; exact hpb },
    rw [← cyclotomic₂_div_prod_eq a b (least_div_pow_pos hp hpa hpb) hbne,
      multiplicity.finset.prod (nat.prime_iff_prime_int.mp hp),
      nat.divisors_eq_proper_divisors_insert_self_of_pos (least_div_pow_pos hp hpa hpb),
      finset.sum_insert (@nat.proper_divisors.not_self_mem _)],
  have : ∀ x ∈ (least_div_pow hp hpa hpb).proper_divisors, multiplicity ↑p (cyclotomic₂ x a b) = 0,
  { intros x hx,
    rcases nat.eq_zero_or_pos x with rfl | hxzero,
    { simp only [cyclotomic₂_zero, multiplicity.one_right (show ¬ is_unit (p : ℤ),
      by simp only [int.of_nat_is_unit, nat.is_unit_iff, nat.prime.ne_one hp, not_false_iff])] },
    { rw multiplicity.multiplicity_eq_zero_of_not_dvd,
      have := least_div_pow_min hp hpa hpb hxzero ((nat.mem_proper_divisors.mp hx).2),
      contrapose! this,
      exact dvd_trans this (cyclotomic₂_dvd_pow_sub x a b hbne) }},
  simp only [finset.sum_congr rfl this, finset.sum_const_zero, add_zero]
end

end cyclotomic₂

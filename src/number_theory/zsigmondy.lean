import ring_theory.polynomial.cyclotomic.eval
import number_theory.multiplicity

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

def least_dvd_pow {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :=
  nat.find (show ∃ k : ℕ, ↑p ∣ a ^ k - b ^ k ∧ 0 < k,
    by refine ⟨p - 1, (prime_div_pow_sub hp hpa hpb), by norm_num [nat.prime.one_lt hp]⟩)

def least_dvd_pow_def {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ (least_dvd_pow hp hpa hpb) - b ^ (least_dvd_pow hp hpa hpb) :=
by simp only [least_dvd_pow, (nat.find_spec (show ∃ k : ℕ, ↑p ∣ a ^ k - b ^ k ∧ 0 < k,
    by refine ⟨p - 1, (prime_div_pow_sub hp hpa hpb), by norm_num [nat.prime.one_lt hp]⟩)).1]

lemma least_dvd_pow_pos {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  0 < least_dvd_pow hp hpa hpb :=
  by simp only [least_dvd_pow, nat.find_pos, nat.not_lt_zero,
  and_false, not_false_iff]

lemma least_dvd_pow_min {p k : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b)
  (hk : 0 < k) :
  k < least_dvd_pow hp hpa hpb → ¬ ↑p ∣ a ^ k - b ^ k :=
begin
 rw [least_dvd_pow],
 intro h,
 have := nat.find_min _ h,
 simpa [not_and, not_lt, le_zero_iff, ne_of_gt hk]
end

lemma least_dvd_pow_min' {p k : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b)
  (hk : 0 < k) : ↑p ∣ a ^ k - b ^ k → least_dvd_pow hp hpa hpb ≤ k :=
by contrapose!; exact least_dvd_pow_min _ _ _ hk

lemma order_of_div_pow_sub {p : ℕ} {a b : ℤ} [fact (nat.prime p)] (hpb : ¬ ↑p ∣ b) :
  ↑p ∣ a ^ order_of ((a / b) : zmod p) - b ^ (order_of ((a / b) : zmod p)) :=
begin
  have hbzero : (b : zmod p) ≠ 0,
  { simp only [ne.def, zmod.int_coe_zmod_eq_zero_iff_dvd, hpb, not_false_iff] },
  rw [← dvd_neg, neg_sub, ←int.modeq_iff_dvd, ←char_p.int_coe_eq_int_coe_iff (zmod p) p,
    int.cast_pow, int.cast_pow, ← (div_eq_one_iff_eq (pow_ne_zero _ hbzero)),
    ← div_pow, pow_order_of_eq_one],
end

lemma least_dvd_pow_zmod_pow_eq {p : ℕ} {a b : ℤ} [hp: fact (nat.prime p)]
  (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b) :
  ((a / b) : zmod p) ^ (least_dvd_pow (fact.elim hp) hpa hpb) = 1 :=
begin
  have hbzero : (b : zmod p) ≠ 0 :=
    by simp only [ne.def, zmod.int_coe_zmod_eq_zero_iff_dvd, hpb, not_false_iff],
    simp_rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hbzero), ← int.cast_pow],
    simp only [char_p.int_coe_eq_int_coe_iff (zmod p) p, int.modeq_iff_dvd, ← dvd_neg,
    neg_sub, least_dvd_pow_def (fact.elim hp) hpa hpb],
end

lemma least_dvd_pow_eq_order {p : ℕ} {a b : ℤ} [hp: fact (nat.prime p)] (hpa : ¬ ↑p ∣ a)
  (hpb : ¬ ↑p ∣ b) :
  least_dvd_pow (fact.elim hp) hpa hpb = order_of ((a / b) : zmod p) :=
begin
  apply le_antisymm _ (order_of_le_of_pow_eq_one (least_dvd_pow_pos (fact.elim hp) hpa hpb)
    (least_dvd_pow_zmod_pow_eq hpa hpb)),
  { have habpos : 0 < order_of ((a / b) : zmod p),
    { rw [order_of_pos_iff, is_of_fin_order_iff_pow_eq_one],
      refine ⟨p - 1, by norm_num [nat.prime.one_lt (fact.elim hp)], _⟩,
      simp only [div_pow, zmod.pow_card_sub_one_eq_one
        (show (b : zmod p) ≠ 0, by simpa [zmod.int_coe_zmod_eq_zero_iff_dvd]),
        zmod.pow_card_sub_one_eq_one (show (a : zmod p) ≠ 0,
        by simpa [zmod.int_coe_zmod_eq_zero_iff_dvd]), one_div_one] },
    exact least_dvd_pow_min' (fact.elim hp) hpa hpb habpos (order_of_div_pow_sub hpb) }
end

lemma least_dvd_pow_dvd {p n : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ n - b ^ n → least_dvd_pow hp hpa hpb ∣ n :=
begin
  have hbzero : (b : zmod p) ≠ 0 :=
    by simp only [ne.def, zmod.int_coe_zmod_eq_zero_iff_dvd, hpb, not_false_iff],
  rcases nat.eq_zero_or_pos n with rfl | hzero,
  { simp only [pow_zero, sub_self, dvd_zero, forall_true_left] },
  { intro hpab,
    haveI : fact (nat.prime p) := fact_iff.mpr hp,
    simp_rw [least_dvd_pow_eq_order hpa hpb, order_of_dvd_iff_pow_eq_one, div_pow,
      div_eq_one_iff_eq (pow_ne_zero _ hbzero), ← int.cast_pow],
    rwa [char_p.int_coe_eq_int_coe_iff (zmod p) p, int.modeq_iff_dvd, ← dvd_neg, neg_sub] }
end

lemma multiplicity_proper_divisors_eq_zero {p x : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a)
  (hpb: ¬ ↑p ∣ b) (hb : b ≠ 0) (hx: x ∈ (least_dvd_pow hp hpa hpb).proper_divisors) :
  multiplicity ↑p (cyclotomic₂ x a b) = 0 :=
begin
  rcases nat.eq_zero_or_pos x with rfl | hxzero,
  { simp only [cyclotomic₂_zero, multiplicity.one_right (show ¬ is_unit (p : ℤ),
    by simp only [int.of_nat_is_unit, nat.is_unit_iff, nat.prime.ne_one hp, not_false_iff])] },
  { rw multiplicity.multiplicity_eq_zero_of_not_dvd,
    have := least_dvd_pow_min hp hpa hpb hxzero ((nat.mem_proper_divisors.mp hx).2),
    contrapose! this,
    exact dvd_trans this (cyclotomic₂_dvd_pow_sub x a b hb) }
end

lemma proposition_10 {p : ℕ} {a b : ℤ} (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b)
  (hp : nat.prime p) :
  multiplicity ↑p (cyclotomic₂ (least_dvd_pow hp hpa hpb) a b) =
  multiplicity ↑p (a ^ (least_dvd_pow hp hpa hpb) - b ^ (least_dvd_pow hp hpa hpb)) :=
begin
  have hbne : b ≠ 0,
  { rintro rfl; simp only [dvd_zero, not_true] at hpb; exact hpb },
    rw [← cyclotomic₂_div_prod_eq a b (least_dvd_pow_pos hp hpa hpb) hbne,
      multiplicity.finset.prod (nat.prime_iff_prime_int.mp hp),
      nat.divisors_eq_proper_divisors_insert_self_of_pos (least_dvd_pow_pos hp hpa hpb),
      finset.sum_insert (@nat.proper_divisors.not_self_mem _)],
  have : ∀ x ∈ (least_dvd_pow hp hpa hpb).proper_divisors, multiplicity ↑p (cyclotomic₂ x a b) = 0 :=
    λ x hx, multiplicity_proper_divisors_eq_zero hp hpa hpb hbne hx,
  simp only [finset.sum_congr rfl this, finset.sum_const_zero, add_zero]
end

lemma lte_version_1 {p β : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b)
  (hpodd : odd p) (hβ : 1 ≤ β) (hb : b ≠ 0) :
  multiplicity ↑p (a ^ (least_dvd_pow hp hpa hpb) - b ^ (least_dvd_pow hp hpa hpb)) + β =
  multiplicity ↑p (a ^ (p ^ β * least_dvd_pow hp hpa hpb) - b ^ (p ^ β * least_dvd_pow hp hpa hpb)) :=
begin
  have : ¬↑p ∣ a ^ (least_dvd_pow hp hpa hpb) :=
  by { intro h; apply hpa; exact prime.dvd_of_dvd_pow (nat.prime_iff_prime_int.mp hp) h },
  simp only [← multiplicity.multiplicity_pow_self (nat.prime.ne_zero hp)
    (prime.not_unit (nat.prime_iff.mp hp)), ← multiplicity.int.pow_sub_pow hp hpodd
    (least_dvd_pow_def hp hpa hpb) this (p ^ β), mul_comm, pow_mul]
end

lemma proposition_11 {p β : ℕ} {a b : ℤ} (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) (hpodd : odd p) (hβ : 1 ≤ β)
  (hp : nat.prime p) (hb : b ≠ 0):
  multiplicity ↑p (a ^ (p ^ β * least_dvd_pow hp hpa hpb) - b ^ (p ^ β * least_dvd_pow hp hpa hpb)) =
  ∑ i in finset.range (β + 1), multiplicity ↑p (cyclotomic₂ (p ^ i * (least_dvd_pow hp hpa hpb)) a b) :=
begin
  rw [← cyclotomic₂_div_prod_eq _ _
    (mul_pos (pow_pos (nat.prime.pos hp) _) (least_dvd_pow_pos hp hpa hpb)) hb,
    multiplicity.finset.prod (nat.prime_iff_prime_int.mp hp)],
  have : ∑ (i : ℕ) in finset.range (β + 1), multiplicity ↑p (cyclotomic₂ (p ^ i * least_dvd_pow hp hpa hpb) a b) =
    ∑ (x : ℕ) in (finset.image (λ i, p ^ i * least_dvd_pow hp hpa hpb) (finset.range (β + 1))), multiplicity ↑p (cyclotomic₂ x a b),
  { simp only [finset.sum_image, mul_right_cancel_iff_of_pos (least_dvd_pow_pos hp hpa hpb),
    function.injective.eq_iff (nat.pow_right_injective (nat.prime.two_le hp)),
    imp_self, implies_true_iff] },
  rw this,
  have hsub : finset.image (λ (i : ℕ), p ^ i * least_dvd_pow hp hpa hpb) (finset.range (β + 1)) ⊆
    (p ^ β * least_dvd_pow hp hpa hpb).divisors,
  { intros i hi,
    simp only [finset.mem_image, finset.mem_range, exists_prop] at hi,
    cases hi with a hia,
    rw [nat.mem_divisors, ← hia.2, mul_dvd_mul_iff_right (ne_of_gt (least_dvd_pow_pos hp hpa hpb))],
    refine ⟨pow_dvd_pow p (nat.le_of_lt_succ hia.1),
      mul_ne_zero (pow_ne_zero β (hp.ne_zero)) (ne_of_gt (least_dvd_pow_pos hp hpa hpb))⟩},
  rw ← finset.sum_sdiff hsub,
  suffices : ∀ x ∈ (p ^ β * least_dvd_pow hp hpa hpb).divisors \ finset.image (λ (i : ℕ),
    p ^ i * least_dvd_pow hp hpa hpb) (finset.range (β + 1)),
    multiplicity ↑p (cyclotomic₂ x a b) = 0,
  { simp only [finset.sum_congr rfl this, finset.sum_const_zero, zero_add] },
  { intros x hx,
    have h : ¬ least_dvd_pow hp hpa hpb ∣ x,
    { intro h,
      cases h with d hd,
      subst hd,
      simp only [mul_ne_zero (pow_ne_zero β hp.ne_zero) (ne_of_gt (least_dvd_pow_pos hp hpa hpb)),
       ne.def, not_false_iff, and_true, finset.mem_sdiff, nat.mem_divisors, finset.mem_image,
       finset.mem_range, not_and, mul_comm _ d,
       mul_dvd_mul_iff_right (ne_of_gt (least_dvd_pow_pos hp hpa hpb)),
       mul_right_cancel_iff_of_pos (least_dvd_pow_pos hp hpa hpb), nat.dvd_prime_pow hp,
       nat.lt_succ_iff, @eq_comm _ d _] at hx,
      exact hx.2 hx.1 },
    rw multiplicity.multiplicity_eq_zero_of_not_dvd,
    contrapose! h,
    replace h := dvd_trans h (cyclotomic₂_dvd_pow_sub x a b hb),
    exact least_dvd_pow_dvd hp hpa hpb h }
end

lemma proposition_12 {p β : ℕ} {a b : ℤ} (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) (hpodd : odd p) (hβ : 1 ≤ β)
  (hp : nat.prime p) (hb : b ≠ 0) (hab : b.nat_abs ≠ a.nat_abs) :
  multiplicity ↑p (cyclotomic₂ (p ^ β * least_dvd_pow hp hpa hpb) a b) = 1 :=
begin
  revert hβ,
  induction β using nat.strong_induction_on with d hind,
  intro h1d,
  have hsub : {0} ⊆ finset.range d := by simp only [nat.succ_le_iff.mp h1d,
    finset.singleton_subset_iff, finset.mem_range],
  have := lte_version_1 hp hpa hpb hpodd h1d hb,
  rw proposition_11 hpa hpb hpodd h1d hp hb at this,
  rw finset.sum_range_succ at this,
  rw ← finset.sum_sdiff hsub at this,
  replace hind : ∀ x ∈ finset.range d \ {0},
    multiplicity ↑p (cyclotomic₂ (p ^ x * least_dvd_pow hp hpa hpb) a b) = 1,
  { intros x hx,
    simp only [finset.mem_sdiff, finset.mem_range, finset.mem_singleton, ← ne.def] at hx,
    exact hind x hx.1 (nat.succ_le_iff.mpr (nat.pos_of_ne_zero hx.2)) },
  have htop : multiplicity ↑p (a ^ least_dvd_pow hp hpa hpb - b ^ least_dvd_pow hp hpa hpb) ≠ ⊤,
  { rw ← multiplicity.int.nat_abs, rw multiplicity.ne_top_iff_finite, rw multiplicity.finite_nat_iff,
    refine ⟨hp.ne_one, int.nat_abs_pos_of_ne_zero _⟩,
    rw [sub_ne_zero, ne.def],
    contrapose! hab,
    replace hab : a.nat_abs ^ least_dvd_pow hp hpa hpb = b.nat_abs ^ least_dvd_pow hp hpa hpb,
    { simp_rw [← int.nat_abs_pow, hab] },
    rw [nat.pow_left_injective (nat.one_le_of_lt (least_dvd_pow_pos hp hpa hpb)) hab] },
  rw [finset.sum_congr rfl hind, finset.sum_const, nsmul_one, finset.sum_singleton, pow_zero,
   one_mul, finset.card_sdiff hsub, finset.card_range, finset.card_singleton,
   proposition_10 hpa hpb hp, add_comm ↑(d - 1), add_assoc,
   part_enat.add_left_cancel_iff htop] at this,
  have hdom : (multiplicity ↑p (cyclotomic₂ (p ^ d * least_dvd_pow hp hpa hpb) a b)).dom,
  { rw [← multiplicity.int.nat_abs, ← multiplicity.finite_iff_dom, multiplicity.finite_nat_iff],
    refine ⟨hp.ne_one, int.nat_abs_pos_of_ne_zero _⟩,
    -- maybe extract separate proof here
    simp only [ne.def, ←(@int.cast_inj) ℝ, ←cyclotomic₂_def', int.cast_zero, cyclotomic₂'],
    have h2le: 2 < p ^ d * least_dvd_pow hp hpa hpb,
    { have hple : p ≤ p ^ d,
      { conv_lhs { rw [← pow_one p] }; exact pow_le_pow (le_of_lt (hp.one_lt)) h1d },
      apply lt_mul_of_lt_of_one_le (lt_of_lt_of_le (lt_of_le_of_ne (hp.two_le) _) hple)
        (nat.succ_le_iff.mp (least_dvd_pow_pos hp hpa hpb)),
      contrapose! hpodd,
      simp only [←hpodd, nat.odd_iff_not_even, even_two, not_true, not_false_iff] },
    have hbpow : (b : ℝ) ^ (p ^ d * least_dvd_pow hp hpa hpb).totient ≠ 0,
    { apply pow_ne_zero; simp only [ne.def, int.cast_eq_zero, hb, not_false_iff] },
    simp only [← ne.def, mul_ne_zero hbpow (ne_of_gt (cyclotomic_pos h2le _)), not_false_iff] },
  rw [← part_enat.coe_get hdom, ← part_enat.coe_coe_hom, ← part_enat.coe_hom.map_add _ _,
   part_enat.coe_coe_hom, part_enat.coe_inj, add_comm, ← (nat.sub_eq_iff_eq_add
   (@tsub_le_self _ _ _ _ d 1)), nat.sub_sub_self h1d] at this,
  rw [← part_enat.coe_get hdom, ← this, nat.cast_one]
end

lemma proposition_13 {p n : ℕ} {a b : ℤ} (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) (hb : b ≠ 0)
  (hp : nat.prime p) (hn : n ∉ {y | ∃ (β : ℕ), p ^ β = y}) :
  multiplicity ↑p (cyclotomic₂ (n * least_dvd_pow hp hpa hpb) a b) = 0 :=
begin
  rcases eq_or_ne n 0 with rfl | hnzero,
  { rw [zero_mul, cyclotomic₂_zero,
     multiplicity.one_right (prime.not_unit (nat.prime_iff_prime_int.mp hp))] },
  { simp only [set.mem_set_of_eq, not_exists] at hn,
    rcases nat.exists_eq_pow_mul_and_not_dvd hnzero p (hp.ne_one) with ⟨β, m, hpm, hmβ⟩,
    subst hmβ,
    have hm : 2 ≤ m,
    { rw nat.two_le_iff,
      refine ⟨(mul_ne_zero_iff.mp hnzero).2, _⟩,
      contrapose! hn,
      refine ⟨β, by rw [hn, mul_one]⟩ },
    },
end

end cyclotomic₂

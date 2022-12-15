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

lemma cyclotomic₂_one_eq (a b : ℤ) (hb : b ≠ 0) : cyclotomic₂ 1 a b = a - b :=
begin
  replace hb : (b : ℝ) ≠ 0 := by simp only [ne.def, int.cast_eq_zero, hb, not_false_iff],
  simp only [←(@ int.cast_inj) ℝ, ←cyclotomic₂_def', cyclotomic₂', nat.totient_one, pow_one,
  cyclotomic_one, eval_sub, eval_X, eval_one, int.cast_sub, mul_sub, mul_one, mul_div_cancel' _ hb]
end

lemma cyclotomic₂_two_eq {a b : ℤ} (hbne : b ≠ 0) : cyclotomic₂ 2 a b = a + b :=
begin
  rcases eq_or_ne b a with rfl | hab,
  { replace hbne : (b : ℝ) ≠ 0 := by norm_num [hbne],
    simp only [←(@ int.cast_inj) ℝ, ←cyclotomic₂_def', cyclotomic₂', nat.totient_two, pow_one,
      cyclotomic_two, eval_add, eval_X, eval_one, int.cast_add, mul_add, div_self hbne, mul_one] },
  { have := cyclotomic₂_div_prod_eq a b (show 0 < 2, by norm_num) hbne,
    rw [← pow_one 2, nat.divisors_prime_pow (nat.prime_two)] at this,
    simp only [finset.prod_map, function.embedding.coe_fn_mk, pow_one, finset.prod_range_succ,
    finset.prod_range_zero, pow_zero, one_mul, sq_sub_sq, cyclotomic₂_one_eq a b hbne,
    mul_comm (a -b)] at this,
    exact mul_right_cancel₀ (sub_ne_zero.mpr (ne.symm hab)) this }
end

lemma prime_div_pow_sub {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ (p - 1) - b ^ (p - 1) :=
by exact int.modeq.dvd (int.modeq.trans (int.modeq.pow_card_sub_one_eq_one hp
    ((prime.coprime_iff_not_dvd (nat.prime_iff_prime_int.mp hp)).mpr hpb).symm)
    ((int.modeq.pow_card_sub_one_eq_one hp ((prime.coprime_iff_not_dvd
    (nat.prime_iff_prime_int.mp hp)).mpr hpa).symm)).symm)


private lemma aux {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b) :
  ∃ k : ℕ, ↑p ∣ a ^ k - b ^ k ∧ 0 < k :=
⟨p - 1, (prime_div_pow_sub hp hpa hpb), by norm_num [nat.prime.one_lt hp]⟩

def least_dvd_pow {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b) :=
nat.find $ aux hp hpa hpb

def least_dvd_pow_def {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ (least_dvd_pow hp hpa hpb) - b ^ (least_dvd_pow hp hpa hpb) :=
(nat.find_spec $ aux hp hpa hpb).1

lemma least_dvd_pow_pos {p : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  0 < least_dvd_pow hp hpa hpb :=
(nat.find_spec $ aux hp hpa hpb).2

namespace tactic
open positivity

/-- Extension for the `positivity` tactic: `least_dvd_pow` is always positive. -/
@[positivity]
meta def positivity_least_dvd_pow : expr → tactic strictness
| `(least_dvd_pow %%hp %%hpa %%hpb) := positive <$> mk_app ``least_dvd_pow_pos [hp, hpa, hpb]
| _ := failed

end tactic

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

-- to PR separately
@[simp, to_additive subsingleton.add_order_of]
lemma subsingleton.order_of {G : Type*} [monoid G] [subsingleton G]
  {x : G} : order_of x = 1 := by rw [subsingleton.elim x 1, order_of_one]

@[to_additive]
lemma is_of_fin_order.is_unit {G : Type*} [monoid G] {x : G} (hx : is_of_fin_order x) : is_unit x :=
begin
  obtain ⟨n, hn⟩ := (is_of_fin_order_iff_pow_eq_one x).mp hx,
  exact is_unit_of_pow_eq_one hn.2 (ne_of_gt hn.1)
end

@[simp]
lemma order_of_non_invertible {G : Type*} [monoid G] {x : G} (hx : ¬ is_unit x) : order_of x = 0 :=
begin
  rw order_of_eq_zero_iff,
  contrapose! hx,
  exact is_of_fin_order.is_unit hx
end

@[simp]
lemma order_of_zero' {G : Type*} [monoid_with_zero G] [nontrivial G]: order_of 0 = 0 :=
begin
  rw order_of_eq_zero_iff',
  intros n hn,
  simp only [ne.def, zero_pow hn, nat.zero_ne_one, not_false_iff]
end

lemma order_of_le_card_univ_sub_one {G : Type*} [fintype G] [group_with_zero G] (x : G) :
  order_of x ≤ fintype.card G - 1 :=
begin
  obtain rfl | hx := eq_or_ne x 0,
  { simp },
  classical,
  rw ← fintype.card_units,
  convert @order_of_le_card_univ _ (units.mk0 _ hx) _ _ using 1,
  rw ← order_of_units,
  simp
end

lemma least_dvd_pow_le {p : ℕ} {a b : ℤ} [hp: fact (nat.prime p)] (hpa : ¬ ↑p ∣ a)
  (hpb : ¬ ↑p ∣ b) :
  least_dvd_pow (fact.elim hp) hpa hpb ≤ p - 1 :=
begin
  rw least_dvd_pow_eq_order hpa hpb,
  convert order_of_le_card_univ_sub_one _,
  simp,
  apply_instance
end
-- end PR

lemma least_dvd_pow_dvd {p n : ℕ} {a b : ℤ} (hp : nat.prime p) (hpa : ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) :
  ↑p ∣ a ^ n - b ^ n ↔ least_dvd_pow hp hpa hpb ∣ n :=
begin
  have hbzero : (b : zmod p) ≠ 0 :=
    by simp only [ne.def, zmod.int_coe_zmod_eq_zero_iff_dvd, hpb, not_false_iff],
  rcases nat.eq_zero_or_pos n with rfl | hzero,
  { simp only [pow_zero, sub_self, dvd_zero, forall_true_left] },
  { haveI : fact (nat.prime p) := fact_iff.mpr hp,
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
  { rw multiplicity.multiplicity_eq_zero,
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
  have := hp.pos,
  rw [← cyclotomic₂_div_prod_eq _ _ (by positivity : 0 < p ^ β * least_dvd_pow hp hpa hpb) hb,
    multiplicity.finset.prod (nat.prime_iff_prime_int.mp hp)],
  have : ∑ (i : ℕ) in finset.range (β + 1), multiplicity ↑p (cyclotomic₂ (p ^ i * least_dvd_pow hp hpa hpb) a b) =
    ∑ x in (finset.image (λ i, p ^ i * least_dvd_pow hp hpa hpb) (finset.range (β + 1))), multiplicity ↑p (cyclotomic₂ x a b),
  { simp only [finset.sum_image, mul_right_cancel_iff_of_pos (least_dvd_pow_pos hp hpa hpb),
      (nat.pow_right_injective hp.two_le).eq_iff, imp_self, implies_true_iff] },
  rw this,
  have hsub : finset.image (λ (i : ℕ), p ^ i * least_dvd_pow hp hpa hpb) (finset.range (β + 1)) ⊆
    (p ^ β * least_dvd_pow hp hpa hpb).divisors,
  { intros i hi,
    simp only [finset.mem_image, finset.mem_range, exists_prop] at hi,
    cases hi with a hia,
    rw [nat.mem_divisors, ← hia.2, mul_dvd_mul_iff_right (ne_of_gt (least_dvd_pow_pos hp hpa hpb))],
    exact ⟨pow_dvd_pow p (nat.le_of_lt_succ hia.1), ne_of_gt $ by positivity⟩ },
  rw ← finset.sum_sdiff hsub,
  suffices : ∀ x ∈ (p ^ β * least_dvd_pow hp hpa hpb).divisors \ finset.image (λ (i : ℕ),
    p ^ i * least_dvd_pow hp hpa hpb) (finset.range (β + 1)),
    multiplicity ↑p (cyclotomic₂ x a b) = 0,
  { simp only [finset.sum_congr rfl this, finset.sum_const_zero, zero_add] },
  { intros x hx,
    have h : ¬ least_dvd_pow hp hpa hpb ∣ x,
    { rintro ⟨d, rfl⟩,
      simp only [mul_ne_zero (pow_ne_zero β hp.ne_zero) (ne_of_gt (least_dvd_pow_pos hp hpa hpb)),
       ne.def, not_false_iff, and_true, finset.mem_sdiff, nat.mem_divisors, finset.mem_image,
       finset.mem_range, not_and, mul_comm _ d,
       mul_dvd_mul_iff_right (ne_of_gt (least_dvd_pow_pos hp hpa hpb)),
       mul_right_cancel_iff_of_pos (least_dvd_pow_pos hp hpa hpb), nat.dvd_prime_pow hp,
       nat.lt_succ_iff, @eq_comm _ d _] at hx,
      exact hx.2 hx.1 },
    rw multiplicity.multiplicity_eq_zero,
    contrapose! h,
    replace h := dvd_trans h (cyclotomic₂_dvd_pow_sub x a b hb),
    exact (least_dvd_pow_dvd hp hpa hpb).mp h }
end

lemma proposition_12 {p β : ℕ} {a b : ℤ} (hpa: ¬ ↑p ∣ a) (hpb: ¬ ↑p ∣ b) (hpodd : odd p) (hβ : 0 < β)
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
  (hp : nat.prime p) (hpodd : odd p) (hab : b.nat_abs ≠ a.nat_abs)
  (hn : ∀ (β : ℕ), n ≠ p ^ β) :
  multiplicity ↑p (cyclotomic₂ (n * least_dvd_pow hp hpa hpb) a b) = 0 :=
begin
  rcases eq_or_ne n 0 with rfl | hnzero,
  { rw [zero_mul, cyclotomic₂_zero,
     multiplicity.one_right (prime.not_unit (nat.prime_iff_prime_int.mp hp))] },
  rcases nat.exists_eq_pow_mul_and_not_dvd hnzero p (hp.ne_one) with ⟨β, m, hpm, hmβ⟩,
  subst hmβ,
  have hm : 2 ≤ m,
  { rw nat.two_le_iff,
    refine ⟨right_ne_zero_of_mul hnzero, _⟩,
    contrapose! hn,
    exact ⟨β, by rw [hn, mul_one]⟩ },
  have hpdiv : ↑p ∣ a ^ (p ^ β * least_dvd_pow hp hpa hpb) - b ^ (p ^ β * least_dvd_pow hp hpa hpb),
  { simp only [least_dvd_pow_dvd hp hpa hpb, dvd_mul_left] },
  have hpapow : ¬ ↑p ∣ a ^ (p ^ β * least_dvd_pow hp hpa hpb) :=
    λ hpapow, hpa (int.prime.dvd_pow' hp hpapow),
  have := hp.pos,
  have hpowpos1 : 0 < p ^ β * least_dvd_pow hp hpa hpb := by positivity,
  have hpowpos2 : 0 < p ^ β * least_dvd_pow hp hpa hpb * m := by positivity,
  suffices hsum : ∑ x in (p ^ β * least_dvd_pow hp hpa hpb * m).divisors \
    (p ^ β * least_dvd_pow hp hpa hpb).divisors, multiplicity ↑p (cyclotomic₂ x a b) = 0,
  { rw finset.sum_eq_zero_iff at hsum,
    refine hsum _ _,
    simp only [finset.mem_sdiff, mul_assoc, mul_comm m, nat.mem_divisors_self _
      (show p ^ β * (least_dvd_pow hp hpa hpb * m) ≠ 0, by linarith), true_and],
    simp only [nat.mem_divisors, not_and, not_ne_iff, ←mul_assoc],
    exact λ hdvd, nat.eq_zero_of_dvd_of_lt hdvd (lt_mul_of_one_lt_right ‹_› hm) },
  have := multiplicity.int.pow_sub_pow hp hpodd hpdiv hpapow m,
  simp only [multiplicity.multiplicity_eq_zero.mpr hpm, add_zero, ← pow_mul,
    ← cyclotomic₂_div_prod_eq _ _ hpowpos1 hb, ← cyclotomic₂_div_prod_eq _ _ hpowpos2 hb,
    multiplicity.finset.prod (nat.prime_iff_prime_int.mp hp), ← finset.sum_sdiff
    (nat.divisors_subset_of_dvd hpowpos2.ne' (dvd_mul_right _ _))] at this,
  rw [← part_enat.add_right_cancel_iff _, zero_add, this],
  rw [← multiplicity.finset.prod (nat.prime_iff_prime_int.mp hp),
    cyclotomic₂_div_prod_eq _ _ hpowpos1 hb, ← multiplicity.int.nat_abs,
    multiplicity.ne_top_iff_finite, multiplicity.finite_nat_iff],
  refine ⟨hp.ne_one, int.nat_abs_pos_of_ne_zero _⟩,
  rw sub_ne_zero,
  refine λ hpow, hab.symm _,
  have := congr_arg int.nat_abs hpow,
  simp_rw [int.nat_abs_pow] at this,
  have honelepow : 1 ≤ p ^ β * least_dvd_pow hp hpa hpb := by linarith [hpowpos1],
  exact nat.pow_left_injective honelepow this
end

lemma proposition_14 {β : ℕ} {a b : ℤ} (hβ : 2 ≤ β) (hbne : b ≠ 0) (ha : odd a) (hb : odd b)
  (hab : a.nat_abs ≠ b.nat_abs) :
  multiplicity 2 (cyclotomic₂ (2 ^ β) a b) = 1 :=
begin
  revert hβ,
  induction β using nat.strong_induction_on with d hind,
  intro h1d,
  have hdvdsub : 2 ∣ a - b := by simp only [← even_iff_two_dvd, ha.sub_odd hb],
  have h2a : ¬ 2 ∣ a := by simp only [← even_iff_two_dvd, ← int.odd_iff_not_even, ha],
  have h2d : even (2 ^ d), simp only [nat.even_pow' (show d ≠ 0, by linarith [h1d]), even_two],
  replace hind : ∀ x ∈ finset.range d \ finset.range 2, multiplicity 2 (cyclotomic₂ (2 ^ x) a b) = 1,
  { intros x hx,
    simp only [finset.mem_sdiff, finset.mem_range, not_lt] at hx,
    exact hind _ hx.1 hx.2 },
  have hlte := multiplicity.int.two_pow_sub_pow hdvdsub h2a h2d,
  simp only [int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one,
    ← cyclotomic₂_div_prod_eq a b (show 0 < 2 ^ d, by positivity) hbne,
    nat.divisors_prime_pow (nat.prime_two), multiplicity.multiplicity_pow_self_of_prime
    (int.prime_two), finset.prod_map, function.embedding.coe_fn_mk,
    multiplicity.finset.prod (int.prime_two), finset.sum_range_succ,
    ← finset.sum_sdiff (finset.range_subset.mpr h1d), finset.range_zero, finset.sum_empty,
    pow_zero, zero_add, pow_one, cyclotomic₂_one_eq a b hbne, cyclotomic₂_two_eq hbne,
    finset.sum_congr rfl hind, finset.sum_const, nsmul_one,
    finset.card_sdiff (finset.range_subset.mpr h1d), finset.card_range, ← add_assoc] at hlte,
  suffices : multiplicity 2 (a + b) + multiplicity 2 (a - b) +
    (↑(d - 2) + (1 : ℕ) + multiplicity 2 (cyclotomic₂ (2 ^ d) a b)) =
    multiplicity 2 (a + b) + multiplicity 2 (a - b) + d,
  { have hdom : (multiplicity 2 (cyclotomic₂ (2 ^ d) a b)).dom,
  { rw [← nat.cast_two, ← multiplicity.int.nat_abs, ← multiplicity.finite_iff_dom, multiplicity.finite_nat_iff],
    refine ⟨by norm_num, int.nat_abs_pos_of_ne_zero _⟩,
    -- maybe extract separate proof here
    simp only [ne.def, ←(@int.cast_inj) ℝ, ←cyclotomic₂_def', int.cast_zero, cyclotomic₂'],
    have h2le: 2 < 2 ^ d,
    { conv_lhs { rw ← pow_one 2 },
      exact pow_lt_pow one_lt_two h1d },
    have hbpow : (b : ℝ) ^ nat.totient (2 ^ d) ≠ 0,
    { apply pow_ne_zero; simp only [ne.def, int.cast_eq_zero, hbne, not_false_iff] },
    simp only [← ne.def, mul_ne_zero hbpow (ne_of_gt (cyclotomic_pos h2le _)), not_false_iff] },
    have hnetop1 : multiplicity 2 (a - b) ≠ ⊤,
    { rw [← nat.cast_two, ← multiplicity.int.nat_abs, multiplicity.ne_top_iff_finite, multiplicity.finite_nat_iff],
      refine ⟨by norm_num, int.nat_abs_pos_of_ne_zero (sub_ne_zero.mpr _)⟩,
      contrapose! hab;  subst hab },
    have hnetop2 : multiplicity 2 (a + b) ≠ ⊤,
    { rw [← nat.cast_two, ← multiplicity.int.nat_abs, multiplicity.ne_top_iff_finite, multiplicity.finite_nat_iff],
      refine ⟨by norm_num, int.nat_abs_pos_of_ne_zero _⟩,
      contrapose! hab,
      rw int.nat_abs_eq_nat_abs_iff,
      right, exact add_eq_zero_iff_eq_neg.mp hab },
    rw [add_assoc, add_assoc, add_assoc, part_enat.add_left_cancel_iff hnetop2,
      part_enat.add_left_cancel_iff hnetop1, ← add_assoc, ← part_enat.coe_get hdom,
      ← part_enat.coe_coe_hom, ← part_enat.coe_hom.map_add, ← part_enat.coe_hom.map_add,
      part_enat.coe_coe_hom, part_enat.coe_inj, ← nat.sub_add_comm h1d,
      nat.succ_sub_succ_eq_sub, ← nat.sub_add_comm (le_trans one_le_two h1d),
      nat.sub_eq_iff_eq_add (le_trans (le_trans one_le_two h1d) (self_le_add_right d _)),
      add_left_cancel_iff] at this,
    rw [← part_enat.coe_get hdom, this, nat.cast_one] },
  { convert hlte using 1,
    -- abel doesn't work here
    rw [nat.cast_one, ← add_assoc, ← add_assoc, ← add_comm ↑(d - 2),
      add_comm (multiplicity 2 (a + b)), add_assoc, add_comm (1 : part_enat), ← add_assoc,
      ← add_assoc] }
end

lemma proposition_15 {n : ℕ} {a b : ℤ} (ha : odd a) (hb : odd b) (hbne : b ≠ 0)
  (hab : b.nat_abs ≠ a.nat_abs) (hn : ∀ (β : ℕ), n ≠ 2 ^ β) :
  multiplicity 2 (cyclotomic₂ n a b) = 0 :=
begin
  rcases eq_or_ne n 0 with rfl | hnzero,
  { rw [cyclotomic₂_zero, multiplicity.one_right (prime.not_unit int.prime_two)] },
  rcases nat.exists_eq_pow_mul_and_not_dvd hnzero 2 (nat.succ_ne_self 1) with ⟨β, m, h2m, hmβ⟩,
  subst hmβ,
  have hm : 2 ≤ m,
  { rw nat.two_le_iff,
    refine ⟨right_ne_zero_of_mul hnzero, _⟩,
    contrapose! hn,
    exact ⟨β, by rw [hn, mul_one]⟩ },
  have h2div : 2 ∣ a - b,
  { simp only [← even_iff_two_dvd, ha.sub_odd hb] },
  have h2a : ¬ 2 ∣ a,
    by simp only [← even_iff_two_dvd, ← int.odd_iff_not_even, ha],
  rcases nat.eq_zero_or_pos β with rfl | hβzero,
  { have h2mint : ¬ 2 ∣ (m : ℤ) := by {norm_cast; assumption},
    have hsub : {1} ⊆ m.divisors,
    { simp only [finset.singleton_subset_iff, nat.mem_divisors, is_unit.dvd, nat.is_unit_iff,
      ne.def, true_and]; linarith [h2m] },
    have hnetop : multiplicity 2 (a - b) ≠ ⊤,
    { rw [← nat.cast_two, ← multiplicity.int.nat_abs, multiplicity.ne_top_iff_finite, multiplicity.finite_nat_iff],
      refine ⟨by norm_num, int.nat_abs_pos_of_ne_zero (sub_ne_zero.mpr _)⟩,
      contrapose! hab;  subst hab },
    have := multiplicity.pow_sub_pow_of_prime (int.prime_two) h2div h2a h2mint,
    rw [← zero_add (multiplicity 2 (a - b)),
      ← cyclotomic₂_div_prod_eq a b (show 0 < m, by linarith) hbne, multiplicity.finset.prod (int.prime_two),
      ← finset.sum_sdiff hsub, finset.sum_singleton, cyclotomic₂_one_eq a b hbne,
      part_enat.add_right_cancel_iff hnetop] at this,
    apply finset.sum_eq_zero_iff.mp this,
    simp only [pow_zero, one_mul, finset.mem_sdiff, nat.mem_divisors, dvd_refl, ne.def, true_and,
      finset.mem_singleton],
    split; linarith [h2m] },
  { have hevenpow1 : even (2 ^ β) := by simp only [even_iff_two_dvd,
      (dvd_pow_self 2 (show β ≠ 0, by linarith))],
    have hevenpow2 : even (2 ^ β * m) := by simp only [even_iff_two_dvd,
      dvd_mul_of_dvd_left (even_iff_two_dvd.mp hevenpow1)],
    have h2mint : ¬ (2 : ℤ) ∣ m := by { norm_cast; exact h2m },
    have hpowpos1 : 0 < 2 ^ β := by positivity,
    have hpowpos2 : 0 < 2 ^ β * m := by positivity,
    have h1netop : (1 : part_enat) ≠ ⊤,
    { simp only [part_enat.ne_top_iff]; exact ⟨1, by norm_cast⟩ },
    have hsubdiv: nat.divisors (2 ^ β) ⊆ (2 ^ β * m).divisors,
    { exact nat.divisors_subset_of_dvd (ne_of_gt hpowpos2) (dvd_mul_right _ _) },
    suffices hsum : ∑ x in (2 ^ β * m).divisors \ ((2 : ℕ) ^ β).divisors,
      multiplicity 2 (cyclotomic₂ x a b) = 0,
    { rw finset.sum_eq_zero_iff at hsum,
      refine hsum _ _,
      simp only [finset.mem_sdiff, mul_assoc, mul_comm m, nat.mem_divisors_self _
        (show 2 ^ β * m ≠ 0, by linarith), true_and],
      simp only [nat.mem_divisors, not_and, not_ne_iff, ←mul_assoc],
      exact λ hdvd, nat.eq_zero_of_dvd_of_lt hdvd (lt_mul_of_one_lt_right ‹_› hm) },
    have h1 := multiplicity.int.two_pow_sub_pow h2div h2a hevenpow1,
    simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one,
      multiplicity.multiplicity_pow_self_of_prime (int.prime_two),
      multiplicity.multiplicity_eq_zero.mpr h2mint, add_zero] at h1,
    have h2 := multiplicity.int.two_pow_sub_pow h2div h2a hevenpow2,
    simp only [nat.cast_mul, int.coe_nat_pow, int.coe_nat_bit0, nat.cast_one,
      multiplicity.mul (int.prime_two), multiplicity.multiplicity_pow_self_of_prime (int.prime_two),
      multiplicity.multiplicity_eq_zero.mpr h2mint, add_zero, ← h1,
      part_enat.add_right_cancel_iff h1netop, ← cyclotomic₂_div_prod_eq a b hpowpos2 hbne,
      multiplicity.finset.prod (int.prime_two), ← finset.sum_sdiff hsubdiv,
      ← multiplicity.finset.prod (int.prime_two) (nat.divisors (2 ^ β)),
      cyclotomic₂_div_prod_eq a b hpowpos1 hbne] at h2,
    have hnetop : multiplicity 2 (a ^ (2 ^ β) - b ^ (2 ^ β)) ≠ ⊤,
    { rw [← nat.cast_two, ← multiplicity.int.nat_abs, multiplicity.ne_top_iff_finite,
        multiplicity.finite_nat_iff],
      refine ⟨by norm_num, int.nat_abs_pos_of_ne_zero (sub_ne_zero.mpr _)⟩,
      contrapose! hab,
      replace hab := congr_arg int.nat_abs (hab.symm),
      simp only [int.nat_abs_pow] at hab,
      exact (nat.pow_left_injective hpowpos1) hab },
    apply (part_enat.add_right_cancel_iff hnetop).mp,
    convert h2; simp only [zero_add] }
end

lemma zsigmondy_2 {a b : ℤ} (hab1 : is_coprime a b) (hab2: a ≠ - b)
  (hpow : (a + b).nat_abs ∉ {y | ∃ (β : ℕ), 2 ^ β = y}) :
  ∃ p, nat.prime p ∧ ↑p ∣ a ^ 2 - b ^ 2 ∧ ¬ ↑p ∣ a - b :=
begin
  contrapose! hpow,
  simp only [set.mem_set_of_eq],
  have : ∀ p, nat.prime p → p ∣ (a + b).nat_abs → p = 2,
  { intros p hp hpdvd,
    replace hpdvd : ↑p ∣ a + b := by exact int.coe_nat_dvd_left.mpr hpdvd,
    have hsqdvd := dvd_mul_of_dvd_left hpdvd (a - b),
    rw ← sq_sub_sq at hsqdvd,
    specialize hpow p hp hsqdvd,
    have ha := dvd_add hpdvd hpow,
    have hb := dvd_sub hpdvd hpow,
    simp only [add_add_sub_cancel, ← two_mul] at ha,
    simp only [add_sub_sub_cancel, ← two_mul] at hb,
    contrapose hab1,
    have hp2n : ¬ (p : ℤ) ∣ 2,
    { contrapose! hab1,
      norm_cast at hab1,
      exact (nat.prime_dvd_prime_iff_eq hp nat.prime_two).mp hab1 },
      replace ha := int.dvd_nat_abs_of_of_nat_dvd
        (or_iff_not_imp_left.mp (prime.dvd_or_dvd (nat.prime_iff_prime_int.mp hp) ha) hp2n),
      replace hb := int.dvd_nat_abs_of_of_nat_dvd
        (or_iff_not_imp_left.mp (prime.dvd_or_dvd (nat.prime_iff_prime_int.mp hp) hb) hp2n),
      rw int.coprime_iff_nat_coprime,
      exact nat.not_coprime_of_dvd_of_dvd (nat.prime.one_lt hp) ha hb },
  replace hab2 : (a + b).nat_abs ≠ 0,
  { simp only [ne.def, int.nat_abs_eq_zero, add_eq_zero_iff_eq_neg, hab2, not_false_iff] },
  exact ⟨_, (eq.symm (nat.eq_prime_pow_of_unique_prime_dvd hab2 this))⟩
end

lemma proposition_16 {a b : ℤ} {n p : ℕ} (hp : nat.prime p) (hn : 2 ≤ n)
  (hpa : ¬ ↑p ∣ a) (hpb : ¬ ↑p ∣ b) (hn2: least_dvd_pow hp hpa hpb < n)
  (hdvd : ↑p ∣ cyclotomic₂ n a b) (hab : b < a) (hb : 0 < b) :
  ∃ (β : ℕ), 0 < β ∧ n = p ^ β * least_dvd_pow hp hpa hpb :=
begin
  obtain heven | hpodd := nat.even_or_odd p,
  { sorry },
  have hcycpos : 0 < cyclotomic₂ n a b :=
    (lt_trans (pow_pos (sub_pos.mpr hab) _) (proposition_6 hn hab hb)),
  have hdvdtrans : ↑p ∣ a ^ n - b ^ n := dvd_trans hdvd (cyclotomic₂_dvd_pow_sub n a b (ne_of_gt hb)),
  have hleastdvd : least_dvd_pow hp hpa hpb ∣ n := (least_dvd_pow_dvd hp hpa hpb).mp hdvdtrans,
  have hmultpos : 1 ≤ multiplicity ↑p (cyclotomic₂ n a b),
  { convert multiplicity.multiplicity_le_multiplicity_of_dvd_left hdvd,
    rw multiplicity.multiplicity_self (not_is_unit_of_not_is_unit_dvd
      (prime.not_unit ((nat.prime_iff_prime_int.mp hp))) hdvd) _,
    apply ne_of_gt hcycpos },
  cases hleastdvd with d hnd,
  have : ∃ β : ℕ, d = p ^ β,
  { contrapose! hmultpos,
    rw [hnd, mul_comm, (proposition_13 hpa hpb (ne_of_gt hb) hp hpodd
      (ne_of_lt (int.nat_abs_lt_nat_abs_of_nonneg_of_lt (le_of_lt hb) hab)) hmultpos)],
    exact zero_lt_one },
  cases this with β hβ,
  refine ⟨β, _, _⟩,
  { contrapose! hn2,
    simp only [le_zero_iff] at hn2,
    rw [hn2, pow_zero] at hβ,
    rw [hnd, hβ, mul_one] },
  { rw [hnd, hβ, mul_comm] }
end

lemma proposition_17 {a b : ℤ} {n : ℕ} (hn : 2 ≤ n) (habcop : is_coprime a b) (hab : b < a)
  (hb : 0 < b) (hnoprim: ∀ (p : ℕ), nat.prime p ∧ ↑p ∣ a ^ n - b ^ n →
    ∃ (k : ℕ), 0 < k ∧ k < n ∧ ↑p ∣ a ^ k - b ^ k) :
  cyclotomic₂ n a b = 1 ∨ ∃ (p : ℕ), nat.prime p ∧ cyclotomic₂ n a b = p ∧ p ∣ n :=
begin
  have hn0: n ≠ 0 := by linarith [hn],
  have hcycpos : 0 < cyclotomic₂ n a b :=
    (lt_trans (pow_pos (sub_pos.mpr hab) _) (proposition_6 hn hab hb)),
  rw or_iff_not_imp_left,
  intro hcycone,
  replace hcycone : 1 ≠ cyclotomic₂ n a b := ne.symm hcycone,
  replace hcycpos := lt_of_le_of_ne (by linarith [hcycpos]) hcycone,
  have hpabdvd : ∀ (p : ℕ), nat.prime p ∧ ↑p ∣ cyclotomic₂ n a b → (¬ ↑p ∣ a ∧ ¬ ↑p ∣ b),
  { rintro p ⟨hp, hpc⟩,
    replace hpc := dvd_trans hpc (cyclotomic₂_dvd_pow_sub n a b (ne_of_gt hb)),
    contrapose! habcop,
    by_cases hpa: ↑p ∣ a,
    { have hpan := dvd_pow hpa hn0,
      replace hpc := dvd_sub hpc hpan,
      simp only [sub_sub_cancel_left, dvd_neg] at hpc,
      replace hpc := prime.dvd_of_dvd_pow (nat.prime_iff_prime_int.mp hp) hpc,
      rw int.coprime_iff_nat_coprime,
      exact nat.not_coprime_of_dvd_of_dvd (nat.prime.one_lt hp)
        (int.coe_nat_dvd_left.mp hpa) (int.coe_nat_dvd_left.mp hpc) },
    { replace habcop := habcop hpa,
      exfalso, apply hpa,
      have hpbn := dvd_pow habcop hn0,
      replace hpc := dvd_add hpc hpbn,
      simp only [sub_add_cancel] at hpc,
      exact prime.dvd_of_dvd_pow (nat.prime_iff_prime_int.mp hp) hpc } },
    have : ∃! (p : ℕ), (nat.prime p ∧ ↑p ∣ cyclotomic₂ n a b),
    sorry { have habs := int.nat_abs_lt_nat_abs_of_nonneg_of_lt (by norm_num) hcycpos,
      norm_num at habs,
      obtain ⟨p, hp⟩ := nat.exists_prime_and_dvd (ne_of_gt habs),
      refine ⟨p, ⟨hp.1, int.of_nat_dvd_of_dvd_nat_abs hp.2⟩, _⟩,
      intros q hq,
      have hpdvd := hpabdvd p ⟨hp.1, int.of_nat_dvd_of_dvd_nat_abs hp.2⟩,
      have hqdvd := hpabdvd q ⟨hq.1, hq.2⟩,
      have hpleast : least_dvd_pow hp.1 hpdvd.1 hpdvd.2 < n,
      { obtain ⟨k, hk0, hkn, hkdvd⟩ := hnoprim p ⟨hp.1, dvd_trans (int.of_nat_dvd_of_dvd_nat_abs hp.2)
          (cyclotomic₂_dvd_pow_sub n a b (ne_of_gt hb))⟩,
        exact lt_of_le_of_lt
          (nat.le_of_dvd hk0 ((least_dvd_pow_dvd hp.1 hpdvd.1 hpdvd.2).mp hkdvd)) hkn },
      have hqleast : least_dvd_pow hq.1 hqdvd.1 hqdvd.2 < n,
      { obtain ⟨k, hk0, hkn, hkdvd⟩ := hnoprim q ⟨hq.1, dvd_trans hq.2
          (cyclotomic₂_dvd_pow_sub n a b (ne_of_gt hb))⟩,
        exact lt_of_le_of_lt
          (nat.le_of_dvd hk0 ((least_dvd_pow_dvd hq.1 hqdvd.1 hqdvd.2).mp hkdvd)) hkn} ,
      obtain ⟨β, hβ0, hnp⟩ := proposition_16 hp.1 hn hpdvd.1 hpdvd.2 hpleast (int.of_nat_dvd_of_dvd_nat_abs hp.2) hab hb,
      obtain ⟨γ, hγ0, hnq⟩ := proposition_16 hq.1 hn hqdvd.1 hqdvd.2 hqleast hq.2 hab hb,
      obtain hpq | rfl | hpq := lt_trichotomy p q,
      { exfalso,
        have : ¬ q ∣ n,
        { rw hnp,
          apply nat.prime.not_dvd_mul hq.1,
          { apply not_imp_not.mpr (nat.prime.dvd_of_dvd_pow hq.1),
            apply not_imp_not.mpr (nat.le_of_dvd (hp.1.pos)),
            exact not_le.mpr hpq },
          { apply not_imp_not.mpr (nat.le_of_dvd (least_dvd_pow_pos hp.1 hpdvd.1 hpdvd.2)),
            haveI : fact (nat.prime p) := fact.mk hp.1,
            exact not_le.mpr (lt_of_le_of_lt (least_dvd_pow_le hpdvd.1 hpdvd.2)
              (lt_of_le_of_lt tsub_le_self hpq)), } },
        apply this,
        rw hnq,
        apply dvd_mul_of_dvd_left (dvd_pow_self q (ne_of_gt hγ0)) },
      { refl },
      { exfalso,
        have : ¬ p ∣ n,
        { rw hnq,
          apply nat.prime.not_dvd_mul hp.1,
          { apply not_imp_not.mpr (nat.prime.dvd_of_dvd_pow hp.1),
            apply not_imp_not.mpr (nat.le_of_dvd (hq.1.pos)),
            exact not_le.mpr hpq },
          { apply not_imp_not.mpr (nat.le_of_dvd (least_dvd_pow_pos hq.1 hqdvd.1 hqdvd.2)),
            haveI : fact (nat.prime q) := fact.mk hq.1,
            exact not_le.mpr (lt_of_le_of_lt (least_dvd_pow_le hqdvd.1 hqdvd.2)
              (lt_of_le_of_lt tsub_le_self hpq)), } },
        apply this,
        rw hnp,
        apply dvd_mul_of_dvd_left (dvd_pow_self p (ne_of_gt hβ0)) }},
    have habs : ((cyclotomic₂ n a b).nat_abs : ℤ) = cyclotomic₂ n a b := int.nat_abs_of_nonneg (by linarith [hcycpos]),
    rw ← habs at this,
    norm_cast at this,
    rw ← is_prime_pow_iff_unique_prime_dvd at this,
    obtain ⟨p, l, hp, hpl⟩ := (is_prime_pow_iff_pow_succ _).mp this,
    simp only [←hpl, int.coe_nat_pow] at habs,
    have hpdvd : ↑p ∣ cyclotomic₂ n a b,
    { simp only [← habs, dvd_pow (dvd_refl _) (nat.succ_ne_zero _)] },
    have hpab := hpabdvd p ⟨nat.prime_iff.mpr hp, hpdvd⟩,
    have hpleast : least_dvd_pow (nat.prime_iff.mpr hp) hpab.1 hpab.2 < n,
    { obtain ⟨k, hk0, hkn, hkdvd⟩ := hnoprim p ⟨nat.prime_iff.mpr hp, dvd_trans hpdvd
          (cyclotomic₂_dvd_pow_sub n a b (ne_of_gt hb))⟩,
        exact lt_of_le_of_lt
          (nat.le_of_dvd hk0 ((least_dvd_pow_dvd (nat.prime_iff.mpr hp) hpab.1 hpab.2).mp hkdvd)) hkn },
    obtain ⟨β, hβ0, hnp⟩ := proposition_16 (nat.prime_iff.mpr hp) hn hpab.1 hpab.2 hpleast hpdvd hab hb,
    obtain rfl | hpodd := nat.prime.eq_two_or_odd' (nat.prime_iff.mpr hp),
    { sorry },
    { have hcycmult := proposition_12 hpab.1 hpab.2 hpodd hβ0 (nat.prime_iff.mpr hp) (ne_of_gt hb)
        (ne_of_lt (int.nat_abs_lt_nat_abs_of_nonneg_of_lt (le_of_lt hb) hab)),
      rw ← hnp at hcycmult,
      refine ⟨p, nat.prime_iff.mpr hp, _, _⟩,
      { rw ← habs at hcycmult,
        rw multiplicity.multiplicity_pow_self_of_prime (nat.prime_iff_prime_int.mp (nat.prime_iff.mpr hp)) _ at hcycmult,
        simp only [nat.cast_add, nat.cast_one] at hcycmult,
        replace hcycmult : ↑l + (1 : part_enat) = 0 + 1 := by simpa,
        rw part_enat.add_right_cancel_iff _ at hcycmult,
        { norm_cast at hcycmult,
          rw [← habs, hcycmult, zero_add, pow_one _] },
        { convert part_enat.coe_ne_top 1 }},
      { rw hnp,
        apply dvd_mul_of_dvd_left (dvd_pow_self p (ne_of_gt hβ0)) } }
end

end cyclotomic₂

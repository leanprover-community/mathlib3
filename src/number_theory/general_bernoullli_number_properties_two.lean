import number_theory.general_bernoullli_number_properties_one

variables (d p m : nat) [fact (0 < d)] [fact (nat.prime p)]
  {R : Type*} [normed_comm_ring R] (χ : dirichlet_character R (d * p^m))

open_locale big_operators
open dirichlet_character

lemma sum_even_character [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 --(n : ℕ) --[fact (0 < n)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) :
  filter.tendsto (λ n, ∑ i in finset.range (d * p^n), ((asso_dirichlet_character
  (dirichlet_character.mul χ ((teichmuller_character_mod_p_change_level p d R m)^k)))
  i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0) :=
begin
  rw metric.tendsto_at_top,
  intros ε hε,
  obtain ⟨z, hz⟩ := exists_mul_mul_mul_lt d p m ε χ na hk hχ hp hε,
  refine ⟨max z m, λ x hx, _⟩,
  rw dist_eq_norm, rw sub_zero,
  cases sum_odd_char d p m χ na hk hχ hp _,
  swap 2, exact x,
  { --rw ← smul_eq_mul at h, rw smul_eq_iff_eq_inv_smul at h,
    --rw mul_comm at h, rw eq_comm at h,
    rw two_mul_eq_inv_two_smul p _ _ h.1, rw norm_smul,
    apply lt_of_le_of_lt (mul_le_mul le_rfl (norm_mul_le _ _)
      (norm_nonneg (↑(d * p ^ x) * w)) (norm_nonneg _)) _,
    rw ← mul_assoc,
    apply lt_of_le_of_lt (mul_le_mul le_rfl h.2 (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (norm_nonneg _))) _, --rw nsmul_eq_mul,
    rw mul_comm _ (k - 1 : ℝ), --rw ← mul_assoc _ (k - 1 : ℝ) _,
    rw ← add_mul, rw mul_mul_mul_comm,
    apply lt_of_le_of_lt _ hz,
    apply mul_le_mul _ _ (mul_nonneg (norm_nonneg _)
      (le_of_lt (dirichlet_character.bound_pos _))) _,
    { apply mul_le_mul le_rfl _ _ (norm_nonneg _),
      { apply add_le_add le_rfl _,
        { exact has_add.to_covariant_class_left ℝ, },
        { exact has_add.to_covariant_class_right ℝ, },
        { have : ((2 : ℕ) : R) = 1 + 1,
          { simp only [nat.cast_bit0, nat.cast_one], refl, },
          rw ← this, repeat { rw ← nat.cast_pow, rw norm_mul_eq p, }, --rw norm_mul_eq p,
          { apply mul_le_mul _ le_rfl (norm_nonneg _) (norm_nonneg _),
            repeat { rw nat.cast_pow, rw norm_pow_eq p, },
            any_goals { apply_instance, },
            apply pow_le_pow_of_le_left (norm_nonneg _) _ _,
            { apply norm_le_of_ge d p (le_trans (le_max_left _ _) hx), apply_instance, apply_instance, }, },
          any_goals { apply_instance, }, }, },
      { apply sub_add_norm_nonneg, assumption, }, },
    { apply mul_le_mul _ le_rfl (le_of_lt (dirichlet_character.bound_pos _)) (norm_nonneg _),
      { apply norm_le_of_ge d p (le_trans (le_max_left _ _) hx), apply_instance, apply_instance, }, },
    { apply mul_nonneg (norm_nonneg _) _,
      apply sub_add_norm_nonneg, assumption, }, },
  { apply le_trans (le_max_right _ _) hx, },
end
-- btw, this still works without the na condition, since in the end, we divide by d*p^x

lemma dirichlet_character.lev_mul_dvd' {B : Type*} [comm_monoid_with_zero B] {n : ℕ}
  (χ ψ : dirichlet_character B n) : lev (mul χ ψ) ∣ n :=
begin
  apply dvd_trans (dirichlet_character.lev_mul_dvd _ _) _,
  rw [lcm_eq_nat_lcm, nat.lcm_self],
end

lemma nat.sub_one_le (n : ℕ) : n - 1 ≤ n := nat.sub_le n 1

example : group ℚ := multiplicative.group

lemma aux_one [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even)
  (hp : 2 < p) (x y : ℕ) : (algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k) * (algebra_map ℚ R)
  (polynomial.eval (↑(y.succ) / ↑(d * p ^ x : ℕ)) (polynomial.bernoulli k)) =
  ((y + 1 : ℕ) : R)^k + ((algebra_map ℚ R) (bernoulli 1 * (k : ℚ))) * ((d * p^x : ℕ) : R) *
  ((y + 1 : ℕ) : R)^k.pred + (d * p^x : ℕ) * (∑ (x_1 : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  (((y + 1 : ℕ) : ℚ) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred)) :=
begin
--  conv_lhs { congr, rw ← ring_hom.to_fun_eq_coe, congr, },
  rw ← (algebra_map ℚ R).map_mul,
  rw polynomial.bernoulli_def,
  rw polynomial.eval_finset_sum,
  rw finset.mul_sum,
  simp only [polynomial.eval_monomial, div_pow, nat.cast_succ],
--    conv_lhs { rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _], apply_congr, },
  simp_rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _],
  simp_rw [mul_assoc],
  rw finset.sum_range_succ_comm,
  rw div_mul_cancel _,
  { rw (algebra_map ℚ R).map_add,
    conv_lhs { congr, skip, rw ← nat.succ_pred_eq_of_pos (pos_of_gt hk),
      rw finset.sum_range_succ_comm, },
    rw div_mul_comm,
    rw (algebra_map ℚ R).map_add, rw add_assoc,
    congr,
    { simp only [nat.choose_self, map_nat_cast, one_mul, ring_hom.map_add, nat.sub_self,
        bernoulli_zero, ring_hom.map_pow, ring_hom.map_one, nat.cast_one], },
    { rw nat.choose_succ_self_right, rw ← nat.succ_eq_add_one,
      rw nat.succ_pred_eq_of_pos (pos_of_gt hk),
      rw nat.pred_eq_sub_one, rw div_eq_mul_inv,
      rw ← pow_sub₀ ((d * p^x : ℕ) : ℚ) _ (nat.sub_le k 1),
      { rw nat.sub_sub_self (le_of_lt hk),
        rw pow_one, rw ← mul_assoc, rw (algebra_map ℚ R).map_mul,
        simp only [map_nat_cast, ring_hom.map_add, ring_hom.map_pow, ring_hom.map_one,
          ring_hom.map_mul], },
      { norm_cast, apply ne_zero_of_lt (mul_prime_pow_pos p d x), }, },
    { rw ring_hom.map_sum, rw pow_succ',
      conv_lhs { apply_congr, skip, rw ← mul_assoc, rw ← mul_assoc, rw ← mul_assoc,
        rw (algebra_map ℚ R).map_mul, },
      rw ← finset.sum_mul, rw mul_comm, rw map_nat_cast,
      conv_rhs { congr, skip, apply_congr, skip, rw ← mul_assoc, rw ← mul_assoc, }, }, },
  { norm_cast, apply pow_ne_zero _ (ne_zero_of_lt (mul_prime_pow_pos p d x)), },
end

lemma norm_mul_pow_pos [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] (x : ℕ) : 0 < ∥((d * p^x : ℕ) : R)∥ :=
begin
  rw norm_pos_iff, norm_cast, apply ne_zero_of_lt (mul_prime_pow_pos p d x),
end

/-lemma exists_just [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even)
  (hp : 2 < p) (x y : ℕ) : ∃ z,
  (algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k) * (algebra_map ℚ R)
  (polynomial.eval (↑(y.succ) / ↑(d * p ^ x : ℕ)) (polynomial.bernoulli k)) =
  ((y + 1 : ℕ) : R)^k + ((algebra_map ℚ R) (bernoulli 1 * (k : ℚ))) * ((d * p^x : ℕ) : R) *
  ((y + 1 : ℕ) : R)^k.pred + (d * p^x : ℕ) * z ∧ ∥z∥ ≤ ∥((d * p^x : ℕ) : R)∥ *
  ⨆ (x_1 : zmod k.pred), ∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
  ↑(k.pred.succ.choose x_1.val) * ( ↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥ :=
begin
  refine ⟨∑ (x_1 : ℕ) in finset.range k.pred, (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) *
    ↑(k.pred.succ.choose x_1) * ((↑y + 1) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred),
    _, _⟩,
  { rw ← (algebra_map ℚ R).map_mul,
    rw polynomial.bernoulli_def,
    rw polynomial.eval_finset_sum,
    rw finset.mul_sum,
    simp only [polynomial.eval_monomial, div_pow, nat.cast_succ],
--    conv_lhs { rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _], apply_congr, },
    simp_rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _],
    simp_rw [mul_assoc],
    rw finset.sum_range_succ_comm,
    rw div_mul_cancel _,
    { rw (algebra_map ℚ R).map_add,
      conv_lhs { congr, skip, rw ← nat.succ_pred_eq_of_pos (pos_of_gt hk),
        rw finset.sum_range_succ_comm, },
      rw div_mul_comm',
      rw (algebra_map ℚ R).map_add, rw add_assoc,
      congr,
      { simp only [nat.choose_self, ring_hom.map_nat_cast, one_mul, ring_hom.map_add, nat.sub_self,
          bernoulli_zero, ring_hom.map_pow, ring_hom.map_one, nat.cast_one], },
      { rw nat.choose_succ_self_right, rw ← nat.succ_eq_add_one,
        rw nat.succ_pred_eq_of_pos (pos_of_gt hk),
        rw nat.pred_eq_sub_one, rw div_eq_mul_inv,
        rw ← pow_sub' ((d * p^x : ℕ) : ℚ) _ (nat.sub_le k 1),
        { rw nat.sub_sub_self (le_of_lt hk),
          rw pow_one, rw ← mul_assoc, rw (algebra_map ℚ R).map_mul,
          simp only [ring_hom.map_nat_cast, ring_hom.map_add, ring_hom.map_pow, ring_hom.map_one,
            ring_hom.map_mul], },
        { norm_cast, apply ne_zero_of_lt (mul_prime_pow_pos p d x), }, },
      { rw ring_hom.map_sum, rw pow_succ',
        conv_lhs { apply_congr, skip, rw ← mul_assoc, rw ← mul_assoc, rw ← mul_assoc,
          rw (algebra_map ℚ R).map_mul, },
        rw ← finset.sum_mul, rw mul_comm, rw ring_hom.map_nat_cast,
        conv_rhs { congr, skip, apply_congr, skip, rw ← mul_assoc, rw ← mul_assoc, }, }, },
    { norm_cast, apply pow_ne_zero _ (ne_zero_of_lt (mul_prime_pow_pos p d x)), }, },
  -- { refine ⟨∥∑ (x_1 : ℕ) in finset.range k.pred, (algebra_map ℚ R)
  --     (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  --     ((↑y + 1) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ (k.pred - 1))∥, _⟩,
  { have le : k.pred = k.pred - 1 + 1,
    { rw nat.sub_add_cancel _, rw nat.pred_eq_sub_one, apply nat.le_pred_of_lt hk, },
    apply le_trans (na _ _) _,
    --apply le_trans _ (norm_mul_le _ _),
    apply csupr_le (λ z, _),
    { apply_instance, },

    conv { congr, congr,
      conv { apply_congr, skip, rw le, rw pow_add, rw pow_one, rw ← mul_assoc,
        rw (algebra_map ℚ R).map_mul, },
      rw [← finset.sum_mul], },
    rw mul_comm, --rw ring_hom.map_nat_cast,
    apply le_trans (norm_mul_le _ _) _,
    convert le_rfl,
    { rw ring_hom.map_nat_cast, },
    { rw ← le, }, },
end

lemma exists_just [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even)
  (hp : 2 < p) (x y : ℕ) : ∃ z,
  (algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k) * (algebra_map ℚ R)
  (polynomial.eval (↑(y.succ) / ↑(d * p ^ x : ℕ)) (polynomial.bernoulli k)) =
  ((y + 1 : ℕ) : R)^k + ((algebra_map ℚ R) (bernoulli 1 * (k : ℚ))) * ((d * p^x : ℕ) : R) *
  ((y + 1 : ℕ) : R)^k.pred + (d * p^x : ℕ) * z ∧ ∃ M : ℝ, ∥z∥ ≤ ∥((d * p^x : ℕ) : R)∥ * M :=
begin
  refine ⟨∑ (x_1 : ℕ) in finset.range k.pred, (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) *
    ↑(k.pred.succ.choose x_1) * ((↑y + 1) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred),
    _, _⟩,
  { rw ← (algebra_map ℚ R).map_mul,
    rw polynomial.bernoulli_def,
    rw polynomial.eval_finset_sum,
    rw finset.mul_sum,
    simp only [polynomial.eval_monomial, div_pow, nat.cast_succ],
--    conv_lhs { rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _], apply_congr, },
    simp_rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _],
    simp_rw [mul_assoc],
    rw finset.sum_range_succ_comm,
    rw div_mul_cancel _,
    { rw (algebra_map ℚ R).map_add,
      conv_lhs { congr, skip, rw ← nat.succ_pred_eq_of_pos (pos_of_gt hk),
        rw finset.sum_range_succ_comm, },
      rw div_mul_comm',
      rw (algebra_map ℚ R).map_add, rw add_assoc,
      congr,
      { simp only [nat.choose_self, ring_hom.map_nat_cast, one_mul, ring_hom.map_add, nat.sub_self,
          bernoulli_zero, ring_hom.map_pow, ring_hom.map_one, nat.cast_one], },
      { rw nat.choose_succ_self_right, rw ← nat.succ_eq_add_one,
        rw nat.succ_pred_eq_of_pos (pos_of_gt hk),
        rw nat.pred_eq_sub_one, rw div_eq_mul_inv,
        rw ← pow_sub' ((d * p^x : ℕ) : ℚ) _ (nat.sub_le k 1),
        { rw nat.sub_sub_self (le_of_lt hk),
          rw pow_one, rw ← mul_assoc, rw (algebra_map ℚ R).map_mul,
          simp only [ring_hom.map_nat_cast, ring_hom.map_add, ring_hom.map_pow, ring_hom.map_one,
            ring_hom.map_mul], },
        { norm_cast, apply ne_zero_of_lt (mul_prime_pow_pos p d x), }, },
      { rw ring_hom.map_sum, rw pow_succ',
        conv_lhs { apply_congr, skip, rw ← mul_assoc, rw ← mul_assoc, rw ← mul_assoc,
          rw (algebra_map ℚ R).map_mul, },
        rw ← finset.sum_mul, rw mul_comm, rw ring_hom.map_nat_cast,
        conv_rhs { congr, skip, apply_congr, skip, rw ← mul_assoc, rw ← mul_assoc, }, }, },
    { norm_cast, apply pow_ne_zero _ (ne_zero_of_lt (mul_prime_pow_pos p d x)), }, },
  { refine ⟨∥∑ (x_1 : ℕ) in finset.range k.pred, (algebra_map ℚ R)
      (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
      ((↑y + 1) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ (k.pred - 1))∥, _⟩,
    have le : k.pred = k.pred - 1 + 1,
    { rw nat.sub_add_cancel _, rw nat.pred_eq_sub_one, apply nat.le_pred_of_lt hk, },
    conv { congr, congr,
      conv { apply_congr, skip, rw le, rw pow_add, rw pow_one, rw ← mul_assoc,
        rw (algebra_map ℚ R).map_mul, },
      rw [← finset.sum_mul], },
    rw mul_comm, --rw ring_hom.map_nat_cast,
    apply le_trans (norm_mul_le _ _) _,
    convert le_rfl,
    { rw ring_hom.map_nat_cast, },
    { rw ← le, }, },
end

lemma spec_nonneg [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even)
  (hp : 2 < p) (x y : ℕ) : 0 ≤ (classical.some (classical.some_spec
    (exists_just d p m χ hk hχ hp x y)).2) :=
begin
  have mul_nn : 0 ≤ ∥((d * p^x : ℕ) : R)∥ * (classical.some (classical.some_spec
    (exists_just d p m χ hk hχ hp x y)).2),
  { have := classical.some_spec (classical.some_spec (exists_just d p m χ hk hχ hp x y)).2,
    apply le_trans _ this,
    apply norm_nonneg _, },
  apply nonneg_of_mul_nonneg_left mul_nn (norm_mul_pow_pos d p x),
end

lemma exists_just_cont' [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even)
  (hp : 2 < p) (x : ℕ) : ∃ (M : ℝ),
  (⨆ (i : zmod (d * p^x)),
  ∥classical.some (exists_just d p m χ hk hχ hp x i.val) ∥) ≤ ∥((d * p^x : ℕ) : R)∥ * M ∧
  0 ≤ M :=
begin
  haveI : fact (0 < d * p^x) := imp p d x,
  refine ⟨_, _, _⟩,
  { exact (⨆ (i : zmod (d * p^x)), (classical.some (classical.some_spec
    (exists_just d p m χ hk hχ hp x i.val)).2)), },
  { apply le_trans (csupr_le_csupr _ _) _,
    swap 3, { intro i,
      apply (classical.some_spec (classical.some_spec
      (exists_just d p m χ hk hχ hp x i.val)).2), },
    { apply set.finite.bdd_above _,
      apply_instance,
      exact set.finite_range (λ (i : zmod (d * p ^ x)), ∥↑(d * p ^ x)∥ * classical.some
        (classical.some_spec (exists_just d p m χ hk hχ hp x i.val)).right), },
    { apply csupr_le (λ y, _),
      { apply_instance, },
      { rw mul_le_mul_left _,
        { apply le_csupr_of_le _ _,
          swap 3, { exact y, },
          { apply le_rfl, },
          { apply set.finite.bdd_above _,
            apply_instance,
            exact set.finite_range (λ (i : zmod (d * p ^ x)), classical.some
              (classical.some_spec (exists_just d p m χ hk hχ hp x i.val)).right), }, },
        { rw norm_pos_iff, norm_cast, apply ne_zero_of_lt (mul_prime_pow_pos p d x), }, }, }, },
  { apply le_csupr_of_le _ _,
    swap 3, { exact 0, },
    { apply spec_nonneg, },
    { apply set.finite.bdd_above _,
      apply_instance,
      exact set.finite_range (λ (i : zmod (d * p ^ x)), classical.some
        (classical.some_spec (exists_just d p m χ hk hχ hp x i.val)).right), }, },
end-/

lemma aux_two [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even)
  (hp : 2 < p) (x y : ℕ) : ∥(∑ (x_1 : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  (((y + 1 : ℕ) : ℚ) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred))∥ ≤
  ∥((d * p^x : ℕ) : R)∥ * (⨆ (x_1 : zmod k.pred), (∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
  ↑(k.pred.succ.choose x_1.val) * ( ↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥)) :=
begin
  have le : k.pred = k.pred - 1 + 1,
  { rw nat.sub_add_cancel _, rw nat.pred_eq_sub_one, apply nat.le_pred_of_lt hk, },
  apply le_trans (na _ _) _,
  --apply le_trans _ (norm_mul_le _ _),
  apply csupr_le (λ z, _),
  { apply_instance, },
  conv { congr, congr, find (↑(d * p ^ x) ^ k.pred) { rw [le], rw pow_add, rw pow_one, }, rw ← mul_assoc,
      rw (algebra_map ℚ R).map_mul, rw mul_assoc _ _ (↑(d * p ^ x) ^ (k.pred - 1)), rw div_mul_comm, },
  rw mul_comm, --rw ring_hom.map_nat_cast,
  apply le_trans (norm_mul_le _ _) _,
  rw map_nat_cast,
  rw mul_le_mul_left _,
--  simp_rw [div_mul_comm'],
  conv { congr, rw ← mul_assoc, rw (algebra_map ℚ R).map_mul, },
  apply le_trans (norm_mul_le _ _) _,
  have padic_le : ∥(algebra_map ℚ R) (((y + 1 : ℕ) : ℚ) ^ z.val)∥ ≤ 1,
  { rw ← nat.cast_pow,
    rw map_nat_cast,
    rw norm_coe_eq_ring_hom_map p,
    apply padic_int.norm_le_one _,
    apply_instance, apply_instance, },
  apply le_trans (mul_le_mul le_rfl padic_le (norm_nonneg _) (norm_nonneg _)) _,
  rw mul_one,
  { refine le_cSup _ _,
    { haveI : fact (0 < k.pred),
      { apply fact_iff.2 (nat.lt_pred_iff.2 hk), },
      apply set.finite.bdd_above,
      exact set.finite_range (λ (x_1 : zmod (nat.pred k)), ∥(algebra_map ℚ R)
         (bernoulli ((nat.pred k).succ - x_1.val) * ↑((nat.pred k).succ.choose x_1.val) *
            (↑(d * p ^ x) ^ (nat.pred k - 1) / ↑(d * p ^ x) ^ x_1.val))∥), },
    { simp only [set.mem_range, exists_apply_eq_apply], }, },
  { exact norm_mul_pow_pos d p x, },
end

lemma finset.neg_sum {α β : Type*} [ring β] (s : finset α) (f : α → β) :
  ∑ x in s, - (f x) = - ∑ x in s, f x :=
begin
  conv_lhs { apply_congr, skip, rw neg_eq_neg_one_mul, },
  rw ← finset.mul_sum, rw ← neg_eq_neg_one_mul,
end

example (a b : R) : a - a - b = -b := by { rw sub_self, rw zero_sub, }
-- #where

-- lemma bla [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
--   [normed_algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R]
--   (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
--   [fact (0 < m)] {k : ℕ} (ε : ℝ) (x : ℕ) (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (hε : ε > 0)
--   (ne_zero : (d * p ^ x) ≠ 0) (coe_sub : ↑k - 1 = ↑(k - 1))
--   --(non_unit : ¬is_unit ↑(d * p ^ x))
--   (h' : ∀ (x : ℕ), (asso_dirichlet_character (χ.mul
--     (teichmuller_character_mod_p_change_level p d R m ^ k)).asso_primitive_character) ↑x =
--     (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑x)
--   (f1 : (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).
--     asso_primitive_character.conductor = (χ.mul (teichmuller_character_mod_p_change_level p d R m ^
--     k)).conductor) : ∥∑ (x_1 : ℕ) in finset.range (d * p ^ x),
--   (1 / ((d * p ^ x : ℕ) : ℚ)) • ((asso_dirichlet_character (χ.mul
--   (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑(x_1.succ) *
--   (↑(d * p ^ x) * classical.some (exists_just d p m _ hk hχ hp x _)))∥ < ε / 2 :=
-- begin
--   sorry
-- end
-- #exit

lemma inv_smul_self [algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
  (n : ℚ)⁻¹ • (n : R) = 1 :=
begin
  rw ← one_mul (n : R), rw ← smul_mul_assoc, rw ← algebra.algebra_map_eq_smul_one,
  have : (algebra_map ℚ R) (n : ℚ) = (n : R), simp only [map_nat_cast],
  conv_lhs { congr, skip, rw ← this, }, rw ← (algebra_map ℚ R).map_mul, rw inv_mul_cancel _,
  simp only [ring_hom.map_one],
  { norm_cast, apply hn, },
end

lemma one_div_smul_self [algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
  (1 / (n : ℚ)) • (n : R) = 1 :=
by { rw [← inv_eq_one_div, inv_smul_self hn], }

lemma norm_asso_dir_char_bound [normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ) (x : ℕ) :
  ⨆ (i : zmod (d * p ^ x)), ∥(asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑(i.val.succ)∥ <
  dirichlet_character.bound (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)) :=
begin
  rw supr_Prop_eq,
  refine ⟨0, dirichlet_character.lt_bound _ _⟩,
end

lemma zmod.val_le_self (a n : ℕ) : (a : zmod n).val ≤ a :=
begin
  cases n,
  { simp only [int.nat_cast_eq_coe_nat], refl, },
  { by_cases a < n.succ,
    rw zmod.val_cast_of_lt h,
    apply le_trans (zmod.val_le _) _,
    { apply succ_pos'' _, },
    { apply le_of_not_gt h, }, },
end

lemma not_is_unit_of_not_coprime {m a : ℕ} (ha : is_unit (a : zmod m)) : nat.coprime a m :=
begin
  have f := zmod.val_coe_unit_coprime (is_unit.unit ha),
  rw is_unit.unit_spec at f,
  have : m ∣ (a - (a : zmod m).val),
  { rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd,
    rw nat.cast_sub (zmod.val_le_self _ _),
    rw sub_eq_zero,
    cases m,
    { simp only [int.coe_nat_inj', int.nat_cast_eq_coe_nat], refl, },
    { rw zmod.nat_cast_val, simp only [zmod.cast_nat_cast'], }, },
  cases this with y hy,
  rw nat.sub_eq_iff_eq_add _ at hy,
  { rw hy, rw add_comm, rw ← nat.is_coprime_iff_coprime,
    simp only [int.coe_nat_add, int.coe_nat_mul],
    rw is_coprime.add_mul_left_left_iff,
    rw nat.is_coprime_iff_coprime,
    convert zmod.val_coe_unit_coprime (is_unit.unit ha), },
  { apply zmod.val_le_self, },
end

/-lemma not_is_unit_mul [normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ) {x : ℕ} (hx : m ≤ x) :
  ¬ is_unit ((d * p^x : ℕ) : zmod (χ.change_level (dvd_lcm_left (d * p^m) (d * p^m)) *
    (teichmuller_character_mod_p_change_level p d R m ^ k).change_level
    (dvd_lcm_right (d * p^m) (d * p^m))).conductor) :=
begin
  intro h,
  have h' := not_is_unit_of_not_coprime h,

  sorry
end-/

lemma norm_lim_eq_zero [normed_algebra ℚ_[p] R] [norm_one_class R] (k : R) :
  filter.tendsto (λ n : ℕ, (((d * p^n) : ℕ) : R) * k) (filter.at_top) (nhds 0) :=
begin
  by_cases k = 0,
  { rw h, simp only [mul_zero], exact tendsto_const_nhds, },
  { rw metric.tendsto_at_top,
    rintros ε hε,
    have f : 0 < ∥k∥⁻¹,
    { rw inv_pos, rw norm_pos_iff, apply h, },
    have f1 : 0 < ∥k∥⁻¹ * ε,
    { apply mul_pos f hε, },
    have f2 : 1/(p : ℝ) < 1,
    { rw one_div_lt _ _,
      { rw one_div_one, norm_cast, apply nat.prime.one_lt, apply fact.out, },
      { norm_cast, apply nat.prime.pos, apply fact.out, },
      { norm_num, }, },
    have f3 : 0 ≤ 1 / (p : ℝ),
    { apply div_nonneg _ _,
      any_goals { norm_cast, apply nat.zero_le _, }, },
    refine ⟨classical.some (exists_pow_lt_of_lt_one f1 f2), λ n hn, _⟩,
    rw dist_eq_norm, rw sub_zero,
    apply lt_of_le_of_lt (norm_mul_le _ _) _,
    apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow d p n) le_rfl (norm_nonneg _) _) _,
    { apply_instance, },
    { apply_instance, },
    { rw ← one_div_pow, apply pow_nonneg f3 _, },
    rw ← inv_inv (∥k∥),
    rw mul_inv_lt_iff f,
    { rw ← one_div_pow,
      apply lt_of_le_of_lt (pow_le_pow_of_le_one f3 (le_of_lt f2) hn) _,
      apply classical.some_spec (exists_pow_lt_of_lt_one f1 f2), }, },
end

lemma norm_lim_eq_zero' [normed_algebra ℚ_[p] R] [norm_one_class R] {ε : ℝ} (hε : 0 < ε) {k : ℝ} (hk : 0 ≤ k) :
  ∃ n : ℕ, ∀ x ≥ n, ∥((d * p^x : ℕ) : R)∥ * k < ε :=
begin
  by_cases k = 0,
  { rw h, simp only [mul_zero, hε], simp only [implies_true_iff, exists_const], },
  { have f : 0 < k⁻¹,
    { rw inv_pos, apply lt_of_le_of_ne hk (ne_comm.1 h), },
    have f1 : 0 < k⁻¹ * ε,
    { apply mul_pos f hε, },
    have f2 : 1/(p : ℝ) < 1,
    { rw one_div_lt _ _,
      { rw one_div_one, norm_cast, apply nat.prime.one_lt, apply fact.out, },
      { norm_cast, apply nat.prime.pos, apply fact.out, },
      { norm_num, }, },
    have f3 : 0 ≤ 1 / (p : ℝ),
    { apply div_nonneg _ _,
      any_goals { norm_cast, apply nat.zero_le _, }, },
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one f1 f2,
    refine ⟨n, λ x hx, _⟩,
    apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow d p x) le_rfl hk _) _,
    { apply_instance, },
    { apply_instance, },
    { rw ← one_div_pow, apply pow_nonneg f3 _, },
    rw ← inv_inv k,
    rw mul_inv_lt_iff f,
    { rw ← one_div_pow,
      apply lt_of_le_of_lt (pow_le_pow_of_le_one f3 (le_of_lt f2) hx) hn, }, },
end

lemma lim_eq_lim [normed_algebra ℚ_[p] R] [norm_one_class R] {a : R} (k : R) {f : ℕ → R}
  (ha : filter.tendsto f (filter.at_top) (nhds a)) :
  filter.tendsto (λ n : ℕ, f n + (((d * p^n) : ℕ) : R) * k) (filter.at_top) (nhds a) :=
begin
  rw ← add_zero a,
  apply filter.tendsto.add ha (norm_lim_eq_zero d p k),
end

noncomputable abbreviation N1 [normed_algebra ℚ_[p] R] [algebra ℚ R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) (ε : ℝ) (hε : 0 < ε) :=
  Inf {n : ℕ | ∀ (x : ℕ) (hx : n ≤ x), ∥(∑ (i : ℕ) in finset.range (d * p ^ x),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i *
  ↑i ^ (k - 1))∥ < ε}

-- lemma N1_nonempty : set.nonempty ({n : ℕ | ∀ (x : ℕ), n ≤ x → ∥∑ (i : ℕ) in finset.range (d * p ^ x),
--     (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i *
--       ↑i ^ (k - 1)∥ < ε})

lemma nat_spec (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

lemma N1_spec [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] [fact (0 < m)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (ε : ℝ) (hε : 0 < ε) (x : ℕ)
  (hx : N1 d p m χ hk ε hε ≤ x) :
  ∥(∑ (i : ℕ) in finset.range (d * p ^ x),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i *
  ↑i ^ (k - 1))∥ < ε :=
begin
  apply nat_spec _ _ x hx,
  refine ⟨classical.some (metric.tendsto_at_top.1 (sum_even_character d p m χ na hk hχ hp) ε hε),
    λ x hx, _⟩,
  rw ← dist_zero_right _,
  apply classical.some_spec (metric.tendsto_at_top.1
    (sum_even_character d p m χ na hk hχ hp) ε hε) x hx,
end

noncomputable abbreviation N2 [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) (ε : ℝ) (hε : 0 < ε) :=
  Inf { n : ℕ | ∀ (x : ℕ) (hx : n ≤ x), ∥((d * p ^ x : ℕ) : R)∥ *
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound < ε}

lemma N2_spec [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] [fact (0 < m)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (ε : ℝ) (hε : 0 < ε) (x : ℕ)
  (hx : N2 d p m χ hk ε hε ≤ x) :
  ∥((d * p ^ x : ℕ) : R)∥ *
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound < ε :=
begin
  apply nat_spec _ _ x hx,
  refine ⟨classical.some (norm_lim_eq_zero' d p hε (le_of_lt (dirichlet_character.bound_pos
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))))), λ x hx, _⟩,
  { exact R, },
  any_goals { apply_instance, },
  apply classical.some_spec (norm_lim_eq_zero' d p hε (le_of_lt (dirichlet_character.bound_pos
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))))) x hx,
end

lemma norm_le_one [normed_algebra ℚ_[p] R][norm_one_class R] (n : ℕ) : ∥(n : R)∥ ≤ 1 :=
begin
  rw norm_coe_eq_ring_hom_map p,
  apply padic_int.norm_le_one,
  apply_instance, apply_instance,
end

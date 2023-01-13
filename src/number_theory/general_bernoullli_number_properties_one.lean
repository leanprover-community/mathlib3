import number_theory.dirichlet_character_properties
import number_theory.bernoulli_measure.bernoulli_measure_seven

-- `mul_eval_coprime` replaced with `mul_eval_of_coprime`
-- `lev_mul_dvd` replaced with `lev_mul_dvd_lcm`
-- `mul_eval_coprime'` replaced with `mul_eval_neg_one`
-- `teichmuller_character_mod_p_change_level_pow` replaced with `dirichlet_character.pow_apply`
-- `teichmuller_character_mod_p_eval_neg_one` replaced with `teichmuller_character.eval_neg_one`
-- removed `asso_dc`

open dirichlet_character zmod

namespace nat
lemma add_sub_pred (n : ℕ) : n + (n - 1) = 2 * n - 1 :=
begin
  cases n,
  { refl, },
  { rw [←nat.add_sub_assoc (nat.succ_le_succ (nat.zero_le _)), nat.succ_mul, one_mul], },
end

lemma two_mul_sub_one_mod_two_eq_one {k : ℕ} (hk : 1 ≤ k) : (2 * k - 1) % 2 = 1 :=
begin
  have : 2 * k - 1 = 2 * k + 1 - 2, { norm_num, },
  rw [this, ←nat.mod_eq_sub_mod (nat.succ_le_succ (one_le_mul one_le_two hk)),
    nat.odd_iff.1 ⟨k, rfl⟩],
end
end nat

variables {p d m : nat} [fact (nat.prime p)] [fact (0 < d)] {R : Type*} [normed_comm_ring R]
  (χ : dirichlet_character R (d * p^m))

-- replaced `neg_one_pow_eq_neg_one` with `neg_one_pow_prime_sub_two_eq_neg_one`
lemma neg_one_pow_prime_sub_two_eq_neg_one (hp : 2 < p) : (-1 : units R)^(p - 2) = -1 :=
begin
  rw ←units.eq_iff,
  simp only [units.coe_neg_one, units.coe_pow],
  rw neg_one_pow_eq_pow_mod_two,
  cases @nat.prime.eq_two_or_odd p (fact.out _),
  { exfalso, apply ne_of_gt hp h, },
  { rw [←nat.mod_eq_sub_mod (le_of_lt hp), h, pow_one], },
end

namespace teichmuller_character
-- replaced `teichmuller_character_mod_p_change_level_eval_neg_one` with
-- `teichmuller_character.change_level_eval_neg_one`
lemma change_level_eval_neg_one [no_zero_divisors R] [algebra ℚ_[p] R] [nontrivial R]
  (hp : 2 < p) [fact (0 < m)] :
  ((teichmuller_character_mod_p_change_level p d R m)) (-1 : units (zmod (d * p^m))) =
  (-1 : units R) :=
begin
  cases dirichlet_character.is_odd_or_is_even (teichmuller_character_mod_p_change_level p d R m),
  { exact h, },
  { exfalso,
    suffices : ((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
      (teichmuller_character_mod_p p)⁻¹) (-1) = 1,
    { simp only [monoid_hom.comp_apply, monoid_hom.inv_apply, map_inv, inv_eq_one] at this,
      rw [teichmuller_character.eval_neg_one hp, ←units.eq_iff, units.coe_map] at this,
      simp only [ring_hom.to_monoid_hom_eq_coe, units.coe_neg_one, ring_hom.coe_monoid_hom,
        map_neg, map_one, units.coe_one] at this,
      apply @nat.cast_add_one_ne_zero R _ _ _ 1,
      rw [←eq_neg_iff_add_eq_zero, nat.cast_one, this], },
    { convert h,
      simp only [units.map, monoid_hom.mk'_apply, ring_hom.coe_monoid_hom, units.coe_neg_one,
        units.val_eq_coe, units.inv_eq_coe_inv, zmod.cast_hom_apply, inv_neg', inv_one],
      have : ((-1 : zmod (d * p^m)) : zmod p) = -1,
      { rw [cast_neg_one, nat.cast_mul, nat.cast_pow, nat_cast_self _, zero_pow (fact.out _),
          mul_zero], rw zero_sub,
        apply_instance, },
      simp_rw [this], refl, }, },
end
.

-- `teichmuller_character_mod_p_change_level_pow_eval_neg_one` replaced with
-- `teichmuller_character.change_level_pow_eval_neg_one`
lemma change_level_pow_eval_neg_one [algebra ℚ_[p] R] [nontrivial R] [no_zero_divisors R]
  [fact (0 < m)] (k : ℕ) (hp : 2 < p) :
  ((teichmuller_character_mod_p_change_level p d R m ^ k) is_unit_one.neg.unit) = (-1) ^ k :=
begin
  have : (is_unit_one.neg.unit : (zmod (d * p^m))ˣ) = -1,
  { rw [←units.eq_iff, is_unit.unit_spec, units.coe_neg_one], },
  rw [dirichlet_character.pow_apply, this, teichmuller_character.change_level_eval_neg_one hp],
  any_goals { apply_instance, },
end
end teichmuller_character

open_locale big_operators
variables (p R) {χ}
variables {p R}
--set_option pp.proofs true

lemma helper_4 (m : ℕ) [fact (0 < m)] :
  lcm (d * p^m) p = d * p^m :=
begin
  rw lcm_eq_left_iff _ _ _,
  apply dvd_mul_of_dvd_right (dvd_pow_self p (nat.ne_zero_of_lt' 0)) d,
  { apply_instance, },
  { rw normalize_eq _, },
end

open dirichlet_character teichmuller_character
-- choosing `teichmuller_character_mod_p_change_level'` as easiest to work with?
lemma sum_eq_neg_sum_add_dvd (hχ : χ.is_even) [algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) {k : ℕ} (hk : 1 ≤ k) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1) = -1 *
  ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y * ↑y ^ (k - 1) +
  ↑(d * p ^ x) * ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p' p R ^ k)) ∣ d * p^m,
  { apply dvd_trans (lev_mul_dvd_lcm _ _) _,
    rw helper_4, },
  rw ←finset.sum_flip,
  conv_lhs { apply_congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H),
    dirichlet_character.asso_dirichlet_character.eval_mul_sub' _ (dvd_trans lev_mul_dvd
    (mul_dvd_mul dvd_rfl (pow_dvd_pow _ hx)))],
    conv { congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H), sub_eq_add_neg,
      add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
      nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
    congr, skip, apply_congr, skip, rw [pow_succ, mul_assoc ↑(d * p^x) _, mul_assoc ↑(d * p^x) _], },
    rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^x) _,
      mul_comm _ ↑(d * p^x), mul_assoc ↑(d * p^x) _ _], },
  rw [finset.sum_add_distrib, ←finset.mul_sum, ←finset.mul_sum],
  refine congr_arg2 _ (congr_arg2 _ _ _) rfl,
  { rw [←int.cast_one, ←int.cast_neg, mul_eval_neg_one, asso_even_dirichlet_character_eval_neg_one
      _ hχ, one_mul, asso_dirichlet_character_eq_char' _ (is_unit.neg (is_unit_one)),
      change_level_pow_eval_neg_one' k hp, units.coe_pow, units.coe_neg_one, ←pow_add,
      nat.add_sub_pred, odd.neg_one_pow _],
    { rw [nat.odd_iff, nat.two_mul_sub_one_mod_two_eq_one hk], },
    any_goals { apply_instance, }, },
  { rw ←finset.sum_flip, },
end

variable (χ)
lemma helper_5 {k : ℕ} (hk : 1 < k) :
  (d * p^m)^(k - 1) = (d * p^m) * (d * p^m)^(k - 2) :=
begin
  conv_rhs { congr, rw ←pow_one (d * p^m), },
  rw [←pow_add],
  congr,
  rw add_comm,
  conv_rhs { rw [nat.sub_succ, ←nat.succ_eq_add_one,
    nat.succ_pred_eq_of_pos (lt_tsub_iff_right.2 _)], skip, apply_congr hk, },
end

variables (p R)
lemma norm_int_le_one [normed_algebra ℚ_[p] R] [norm_one_class R] (z : ℤ) : ∥(z : R)∥ ≤ 1 :=
begin
  rw [← ring_hom.map_int_cast (algebra_map ℚ_[p] R), ←padic_int.coe_coe_int,
    norm_algebra_map, norm_one_class.norm_one, mul_one],
  apply padic_int.norm_le_one,
end

variables {p R χ}
lemma norm_sum_le_smul {k : ℕ} [normed_algebra ℚ_[p] R] [norm_one_class R] (hk : 1 < k) {x : ℕ}
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  ∥∑ (y : ℕ) in finset.range (d * p ^ x + 1), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ k))) ((-1) * ↑y) *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))∥ ≤ (dirichlet_character.bound
  (χ.mul (teichmuller_character_mod_p' p R ^ k)) * (k - 1)) :=
begin
  have : ∀ y ∈ finset.range (d * p ^ x + 1), ∥(asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p' p R ^ k))) ((-1) * ↑y) *
    ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y)^(k - 1 - (x_1 + 1)) *
    ↑((k - 1).choose (x_1 + 1)) ∥ ≤ (dirichlet_character.bound (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) * (k - 1),
  { intros l hl,
    refine le_trans (norm_mul_le _ _) (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) _
      (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))),
    simp_rw [mul_pow, mul_left_comm, mul_assoc],
    apply le_trans (norm_sum_le _ _) _,
    have : ∀ a ∈ finset.range (k - 1), ∥(-1 : R) ^ (k - 1 - (a + 1)) * (↑(d * p ^ x) ^ a *
      (↑l ^ (k - 1 - (a + 1)) * ↑((k - 1).choose (a + 1))))∥ ≤ 1,
    { intros a ha,
      rw [←int.cast_one, ←int.cast_neg, ←int.cast_pow],
      simp_rw [←nat.cast_pow, ←nat.cast_mul, ←int.cast_coe_nat, ←int.cast_mul],
      apply norm_int_le_one p R, },
    refine le_trans (finset.sum_le_sum this) _,
    rw [finset.sum_const, finset.card_range, nat.smul_one_eq_coe, nat.cast_sub (le_of_lt hk),
      nat.cast_one], },
  refine le_trans (na _ _) (cSup_le (set.range_nonempty _)
    (λ b ⟨y, hy⟩, hy ▸ this y.val (finset.mem_range.2 (zmod.val_lt _)))),
end

-- `sum_odd_char` replaced with `helper_11`
lemma helper_11 [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
 [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {x : ℕ} (hx : m ≤ x) :
 ∃ y, (2 : R) * ∑ i in finset.range (d * p^x), ((asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) i * i^(k - 1)) = ↑(d * p^x) * y ∧ ∥y∥ ≤ ((χ.mul
  (teichmuller_character_mod_p' p R ^ k)).bound * (↑k - 1)) + ∥(((d * p ^ x : ℕ) : R) ^ (k - 2)) *
  (1 + 1)∥ * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound :=
begin
  have f1 : ∑ (i : ℕ) in finset.range (d * p ^ x), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1) =
    ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1)
   - ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(d * p^x) *
   ↑(d * p^x) ^ (k - 1)),
  { rw [finset.sum_range_succ, add_sub_cancel], },
  rw [f1, mul_sub, mul_comm _ (↑(d * p ^ x) ^ (k - 1)), ←mul_assoc _ (↑(d * p ^ x) ^ (k - 1)) _,
    mul_comm _ (↑(d * p ^ x) ^ (k - 1)), mul_assoc _ (2 : R) _, ←nat.cast_pow],
  clear f1,
  conv { congr, funext, rw [sub_eq_iff_eq_add, @helper_5 p d _ _ _ k hk,
    nat.cast_mul (d * p^x) _, mul_assoc ↑(d * p^x) _ _],
    conv { congr, rw ←mul_add ↑(d * p^x) _ _, }, },
  have two_eq_one_add_one : (2 : R) = (1 : R) + (1 : R) := rfl,
  rw [two_eq_one_add_one, add_mul, one_mul],
  conv { congr, funext, conv { congr, to_lhs, congr, skip,
    rw sum_eq_neg_sum_add_dvd hχ hp (le_of_lt hk) hx, }, },
  rw [←neg_eq_neg_one_mul, ←add_assoc, ←sub_eq_add_neg],
  conv { congr, funext, rw [sub_self _, zero_add], },
  refine ⟨∑ (y : ℕ) in finset.range (d * p ^ x + 1),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) (-1) *
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
    ∑ (x_1 : ℕ) in finset.range (k - 1),
    ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1))) -
    ↑((d * p ^ x) ^ (k - 2)) * ((1 + 1) * (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑(d * p ^ x)), _, _⟩,
  { rw sub_add_cancel, },
  { apply le_trans (norm_sub_le _ _) _,
    conv { congr, congr, congr, apply_congr, skip, rw [←mul_assoc, ←monoid_hom.map_mul], },
    apply le_trans (add_le_add (norm_sum_le_smul hk na) (le_refl _)) _,
    { apply_instance, },
    rw ← mul_assoc,
    refine le_trans (add_le_add (le_refl _) (norm_mul_le _ _)) (le_trans (add_le_add (le_refl _)
      ((mul_le_mul_left _).2 (le_of_lt (dirichlet_character.lt_bound _ _)))) _),
    { haveI : algebra ℚ_[p] R, apply_instance, -- needed for char_zero
      refine lt_iff_le_and_ne.2 ⟨norm_nonneg _, λ h, _⟩,
      rw [eq_comm, norm_eq_zero, mul_eq_zero] at h,
      cases h,
      { refine pow_ne_zero _ (ne_zero_of_lt (nat.mul_prime_pow_pos _)) (nat.cast_eq_zero.1 h), },
      { apply zero_ne_one ((self_eq_neg R R).1 (eq_neg_iff_add_eq_zero.2 h)).symm, }, },
    { rw nat.cast_pow, }, },
end

variable (p)
-- `two_mul_eq_inv_two_smul` replaced with `helper_6`
-- can be generalized to n : ℕ and z : ℤ, possibly more
lemma helper_6 [algebra ℚ_[p] R] {a b : R} (h : (2 : R) * a = b) : a = (2 : ℚ_[p])⁻¹ • b :=
begin
  symmetry,
  rw inv_smul_eq_iff₀ _,
  { rw [←h, ←nat.cast_two, ←map_nat_cast (algebra_map ℚ_[p] R) 2, ←smul_eq_mul, algebra_map_smul,
      nat.cast_two], },
  { apply two_ne_zero', },
end

variables (d R)
-- `coe_eq_ring_hom_map` replaced with `nat_coe_eq_ring_hom_map`
lemma nat_coe_eq_ring_hom_map [normed_algebra ℚ_[p] R] (y : ℕ) :
  (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (y : ℤ_[p])) = ((y : ℕ) : R) := by { simp }

-- `norm_coe_eq_ring_hom_map` replaced with `norm_coe_nat_eq_norm_ring_hom_map`
lemma norm_coe_nat_eq_norm_ring_hom_map [normed_algebra ℚ_[p] R]  [norm_one_class R] (y : ℕ) :
  ∥((y : ℕ) : R)∥ = ∥padic_int.coe.ring_hom (y : ℤ_[p])∥ :=
by { rw [←nat_coe_eq_ring_hom_map p R y, norm_algebra_map, norm_one_class.norm_one, mul_one], }

lemma norm_mul_pow_le_one_div_pow [normed_algebra ℚ_[p] R] [norm_one_class R] (y : ℕ) :
  ∥((d * p^y : ℕ) : R)∥ ≤ 1 / p^y :=
begin
  rw nat.cast_mul,
  apply le_trans (norm_mul_le _ _) _,
  rw ← one_mul (1 / (p : ℝ)^y),
  apply mul_le_mul _ _ (norm_nonneg _) zero_le_one,
  { rw norm_coe_nat_eq_norm_ring_hom_map p,
    apply padic_int.norm_le_one,  },
  { apply le_of_eq,
    rw norm_coe_nat_eq_norm_ring_hom_map p,
    simp only [one_div, map_nat_cast, norm_pow, ring_hom.map_pow, inv_pow,
      nat.cast_pow, padic_norm_e.norm_p], },
end

variables {p d R}
-- `norm_mul_two_le_one` replaced with `hlper_7`
lemma helper_7 [normed_algebra ℚ_[p] R] [norm_one_class R] (k : ℕ) (y : ℕ) :
  ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥ ≤ 1 :=
begin
  rw [←nat.cast_pow, ←@nat.cast_one R _ _, ←nat.cast_add, ←nat.cast_mul,
    norm_coe_nat_eq_norm_ring_hom_map p],
  apply padic_int.norm_le_one _,
end

-- `sub_add_norm_nonneg` replaced with `helper_8`
lemma helper_8 {k : ℕ} (hk : 1 < k) (y : ℕ) :
  0 ≤ (k : ℝ) - 1 + ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥ :=
begin
  apply add_nonneg _ (norm_nonneg _),
  rw [le_sub_iff_add_le, zero_add],
  norm_cast,
  apply le_of_lt hk,
end

-- `norm_two_mul_le` replaced with `helper_9`
lemma helper_9 [normed_algebra ℚ_[p] R] [norm_one_class R] {k : ℕ} (hk : 1 < k) (hp : 2 < p)
  (y : ℕ) : ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥) ≤ k :=
begin
  rw ← one_mul ↑k,
  apply mul_le_mul (le_of_eq _) _ _ _,
  { rw [norm_inv, inv_eq_one],
    have : ((2 : ℕ) : ℚ_[p]) = (2 : ℚ_[p]), norm_cast,
    rw [←this, ←rat.cast_coe_nat, padic_norm_e.eq_padic_norm,
      padic_norm.padic_norm_of_prime_of_ne (λ h, ne_of_lt hp h.symm), rat.cast_one], },
  { rw one_mul,
    apply le_trans (add_le_add le_rfl (helper_7 k _)) _,
    any_goals { apply_instance, }, --why is this a problem?
    rw sub_add_cancel, },
  { rw one_mul,
    convert helper_8 hk y,
    any_goals { apply_instance, }, },
  { linarith, },
end

variable (χ)
-- `exists_mul_mul_mul_lt` replaced with `helper_10`
lemma helper_10 [normed_algebra ℚ_[p] R] [norm_one_class R] {k : ℕ} {ε : ℝ} (hk : 1 < k)
  (hp : 2 < p) (hε : ε > 0) : ∃ x : ℕ,
  ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ x : ℕ) : R)^(k - 2) * (1 + 1)∥) *
  (∥(((d * p ^ x) : ℕ) : R)∥ * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) < ε :=
begin
  have one_div_lt_one : 1 / (p : ℝ) < 1,
  { refine (one_div_lt _ _).2 _,
    { refine nat.cast_pos.2 (nat.prime.pos (fact.out _)), },
    { refine zero_lt_one, },
    { rw one_div_one, refine nat.one_lt_cast.2 (nat.prime.one_lt (fact.out _)), }, },
  have pos' : 0 < ↑k * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
  { apply mul_pos (nat.cast_pos.2 (lt_trans zero_lt_one hk)) (dirichlet_character.bound_pos _), },
  have pos : 0 < ε / (↑k * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) := div_pos hε pos',
  refine ⟨classical.some (exists_pow_lt_of_lt_one pos one_div_lt_one), lt_of_le_of_lt (mul_le_mul
    (helper_9 hk hp _) le_rfl (mul_nonneg (norm_nonneg _)
    (le_of_lt (dirichlet_character.bound_pos _))) (nat.cast_nonneg _)) _⟩,
  rw mul_left_comm,
  refine lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow p d R _) le_rfl
    (le_of_lt pos') _) _,
  { rw ←one_div_pow,
    refine pow_nonneg (div_nonneg zero_le_one (nat.cast_nonneg _)) _, },
  { rw ←one_div_pow,
    have := classical.some_spec (exists_pow_lt_of_lt_one pos one_div_lt_one),
    apply lt_of_lt_of_le (mul_lt_mul this le_rfl pos' (div_nonneg (le_of_lt hε) (le_of_lt pos'))) _,
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self (λ h, _), mul_one],
    rw mul_eq_zero at h,
    cases h,
    { rw (nat.cast_eq_zero.1 h) at hk,
      simp only [not_lt_zero'] at hk,
      apply hk, },
    { have := (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound_pos,
      rw h at this,
      simp only [lt_self_iff_false] at this,
      exact this, }, },
end

variables (p R) {χ}
-- `norm_mul_eq` replaced with `norm_mul_nat_eq_mul_norm`
lemma norm_mul_nat_eq_mul_norm [normed_algebra ℚ_[p] R] [norm_one_class R] (x y : ℕ) :
  ∥(x * y : R)∥ = ∥(x : R)∥ * ∥(y : R)∥ :=
by { rw [←nat.cast_mul, norm_coe_nat_eq_norm_ring_hom_map p, nat.cast_mul,
  ring_hom.map_mul padic_int.coe.ring_hom, padic_norm_e.mul, ←norm_coe_nat_eq_norm_ring_hom_map p R,
  ←norm_coe_nat_eq_norm_ring_hom_map p R], }

-- `norm_pow_eq` replaced with `norm_pow_nat_eq_pow_norm`
lemma norm_pow_nat_eq_pow_norm [normed_algebra ℚ_[p] R] [norm_one_class R] (x n : ℕ) :
  ∥(x ^ n : R)∥ = ∥(x : R)∥^n :=
by { rw [←nat.cast_pow, norm_coe_nat_eq_norm_ring_hom_map p, nat.cast_pow, ring_hom.map_pow,
  norm_pow, ← norm_coe_nat_eq_norm_ring_hom_map p R], }

-- `norm_le_of_ge` replaced with `norm_mul_prime_pow_le_of_ge`
lemma norm_mul_prime_pow_le_of_ge [normed_algebra ℚ_[p] R] [norm_one_class R] {x y : ℕ}
  (h : x ≤ y) : ∥((d * p^y : ℕ) : R)∥ ≤ ∥((d * p^x : ℕ) : R)∥ :=
begin
  simp_rw [nat.cast_mul, norm_mul_nat_eq_mul_norm p R, nat.cast_pow],
  apply mul_le_mul le_rfl _ (norm_nonneg _) (norm_nonneg _),
  simp_rw [norm_pow_nat_eq_pow_norm p R, norm_coe_nat_eq_norm_ring_hom_map p],
  simp only [map_nat_cast, norm_pow, ring_hom.map_pow, inv_pow, nat.cast_pow, padic_norm_e.norm_p],
  rw inv_le_inv _ _,
  { refine pow_le_pow (nat.one_le_cast.2 (le_of_lt (nat.prime.one_lt (fact.out _)))) h, },
  any_goals { norm_cast, apply pow_pos _ _, apply nat.prime.pos _, apply fact.out, },
end

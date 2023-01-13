/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_measure.bernoulli_measure_two

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} [fact p.prime] {d : ℕ}
variables (R : Type*) [normed_comm_ring R]
variables {c : ℕ}

set_option old_structure_cmd true

open_locale big_operators

/-- A variant of `zmod` which has type `finset _`. -/
def zmod' (n : ℕ) (h : 0 < n) : finset (zmod n) :=
  @finset.univ _ (@zmod.fintype n (fact_iff.2 h))

namespace nat
lemma mul_prime_pow_pos [fact (0 < d)] (m : ℕ) : 0 < d * p^m := fact.out _

lemma mul_pow_lt_mul_pow_succ [fact (0 < d)] (m : ℕ) : d * p ^ m < d * p ^ m.succ :=
mul_lt_mul' le_rfl (nat.pow_lt_pow_succ (nat.prime.one_lt (fact_iff.1 infer_instance)) m)
    (nat.zero_le _) (fact_iff.1 infer_instance)

end nat

open nat padic_int zmod discrete_quotient_of_to_zmod_pow

lemma zmod'_succ_eq_bUnion_equi_class [fact (0 < d)] (m : ℕ) :
  zmod' (d * (p^m.succ)) (mul_prime_pow_pos m.succ) = (zmod' (d*p^m) (mul_prime_pow_pos m)).bUnion
    (λ a : zmod (d * p ^ m), set.to_finset ((equi_class m.succ) a)) :=
finset.ext (λ y, iff.trans begin simp only [exists_prop, set.mem_to_finset],
  refine ⟨λ h, ⟨(y : zmod (d * p^m)), finset.mem_univ y, (mem_equi_class _ _).2 rfl⟩,
    λ h, finset.mem_univ y⟩, end (iff.symm finset.mem_bUnion))

lemma equi_class_eq [fact (0 < d)] {m : ℕ} (hd : d.coprime p)
  {f : locally_constant (zmod d × ℤ_[p]) R} (h : classical.some (le hd f) ≤ m) (x : zmod (d * p^m))
  (y : zmod (d * p^m.succ))
  (hy : y ∈ set.to_finset ((equi_class m.succ) x)) : f y = f x :=
begin
  -- note that y ≠ ↑x !
  rw [set.mem_to_finset, mem_equi_class] at hy,
  rw [←locally_constant.factors, function.comp_apply],
  apply congr_arg,
  have h' := classical.some_spec (le hd f),
  rw [←discrete_quotient.of_le_proj (le_trans (le_of_ge p d h) h'), function.comp_apply],
  refine congr_arg _ _,
  change ↑y ∈ ((discrete_quotient_of_to_zmod_pow p d m).proj)⁻¹'
    {(discrete_quotient_of_to_zmod_pow p d m).proj x},
  simp_rw [discrete_quotient.fiber_eq, set.mem_set_of_eq, discrete_quotient_of_to_zmod_pow.rel,
    prod.fst_zmod_cast, prod.snd_zmod_cast, ←hy],
  have val_le_val : (y.val : zmod (d * p^m)).val ≤ y.val := val_coe_val_le_val _,
  have dvds : (d * p^m) ∣ y.val - (y.val : zmod (d * p^m)).val,
  { rw [←zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.cast_sub val_le_val],
    simp only [zmod.cast_id', id.def, sub_self, zmod.nat_cast_val], },
  split,
  { rw [←sub_eq_zero, ←ring_hom.map_sub, ←ring_hom.mem_ker, ker_to_zmod_pow,
      ideal.mem_span_singleton],
    repeat { rw ←zmod.nat_cast_val, },
    rw [←dvd_neg, neg_sub, ←nat.cast_pow, ←nat.cast_sub val_le_val],
    apply nat.coe_nat_dvd (dvd_trans (dvd_mul_left _ _) dvds), },
  { repeat { rw ←zmod.nat_cast_val, },
    rw [zmod.nat_coe_eq_nat_coe_iff, nat.modeq_iff_dvd' val_le_val],
    apply dvd_trans (dvd_mul_right _ _) dvds, },
end
-- This lemma has a lot of mini lemmas that can be generalized.

lemma card_equi_class [fact (0 < d)] {m : ℕ} (x : zmod (d * p^m)) :
  finset.card (@finset.univ (equi_class m.succ x) _) = p :=
begin
  rw [finset.card_univ, ←fintype.of_equiv_card (equi_iso_fin m x)],
  convert fintype.card_fin p,
end

namespace int
lemma fract_eq_self' {a : ℚ} (h : 0 ≤ a) (ha : a < 1) : int.fract a = a :=
int.fract_eq_iff.2 ⟨h, ha, ⟨0, by simp⟩⟩

end int

namespace finset

lemma sum_equiv {α β γ : Type*} {s : finset α} {s' : finset β} {φ : s ≃ s'} {f : α → γ}
  [add_comm_monoid γ] : ∑ x : s, f x = ∑ y : s', f(φ.inv_fun y) :=
begin
  apply finset.sum_bij',
  swap 4, { rintros, exact φ.to_fun a, },
  swap 5, { rintros, exact φ.inv_fun a, },
  all_goals { simp },
end
end finset

lemma sum_rat_fin (n : ℕ) : (((∑ (x : fin n), (x : ℤ)) : ℤ) : ℚ) = (n - 1) * (n : ℚ) / 2 :=
begin
  have : ∀ (x : fin n), (x : ℤ) = ((x : ℕ) : ℤ),
  { simp only [_root_.coe_coe, eq_self_iff_true, implies_true_iff], },
  conv_lhs { congr, congr, skip, funext, rw this x, },
  rw ←finset.sum_range,
  induction n with d hd,
  { simp only [finset.range_zero, finset.sum_empty, int.cast_zero, nat.cast_zero, mul_zero,
      zero_div], },
  { rw [finset.sum_range_succ, int.cast_add, hd _],
    { simp only [int.cast_coe_nat, cast_succ, add_tsub_cancel_right],
      rw div_add',
      { rw [mul_comm _ (d : ℚ), ←mul_add], ring, },
      { simp only [ne.def, bit0_eq_zero, one_ne_zero, not_false_iff], }, },
    { simp only [_root_.coe_coe, eq_self_iff_true, implies_true_iff], }, },
end

namespace nat
lemma lt_pow {n a : ℕ} (h1 : 1 < a) (h2 : 1 < n) : a < a^n :=
begin
  conv { congr, rw ←pow_one a, skip, skip, },
  apply pow_lt_pow h1 h2,
end

lemma le_pow {n a : ℕ} (h1 : 1 ≤ a) (h2 : 1 ≤ n) : a ≤ a^n :=
begin
  conv { congr, rw ←pow_one a, skip, skip, },
  apply pow_le_pow h1 h2,
end

lemma pow_lt_mul_pow_succ_right [fact (0 < d)] (m : ℕ) : p ^ m < d * p ^ m.succ :=
begin
  rw [pow_succ, ←mul_assoc],
  apply lt_mul_of_one_lt_left (pow_pos (nat.prime.pos (fact.out _)) _)
    (one_lt_mul ((nat.succ_le_iff).2 (fact.out _)) (nat.prime.one_lt (fact.out _))),
  all_goals { assumption, },
end

lemma lt_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m :=
lt_of_le_of_lt ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_lt_mul' le_rfl (nat.lt_pow h2 h3) (nat.zero_le _) h1)

lemma le_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 ≤ m) : a ≤ b * a^m :=
le_trans ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_le_mul' le_rfl (nat.le_pow (le_of_lt h2) h3))

lemma cast_eq_coe_b (x : ℕ) : @nat.cast ℤ _ _ _ x = coe_b x :=
begin
  induction x with d hd,
  { change 0 = @has_coe.coe ℕ ℤ _ 0,
    change _ = int.of_nat 0,
    simp only [int.coe_nat_zero, int.of_nat_eq_coe], },
  { show d.cast + 1 = @has_coe.coe ℕ ℤ _ d.succ,
    change _ = int.of_nat d.succ,
    simp only [int.of_nat_eq_coe, int.coe_nat_succ, add_left_inj],
    change _ = int.of_nat d at hd, simp [hd], },
end

end nat

open nat

lemma equi_iso_fun_inv_val [fact (0 < d)] {m : ℕ} (x : zmod (d * p^m)) (k : fin p) :
  ((equi_iso_fin m x).inv_fun k).val = x.val + ↑k * (d * p^m) :=
by { unfold equi_iso_fin, dsimp, norm_cast, rw mul_assoc, }

variables (p d)
lemma helper_2 [fact (0 < d)] (m : ℕ) (y : fin p) : ((y * (d * p ^ m) : zmod (d * p^m.succ)) : ℤ) =
  ↑y * (↑(d : zmod (d * p^m.succ)) * ↑(p : zmod (d * p^m.succ))^m) :=
begin
  have prime_gt_one : 1 < p := prime.one_lt (fact.out _),
  have le_mul_p : p ≤ d * p^m.succ,
  { rw mul_comm,
    apply le_mul_of_le_of_one_le (le_pow (le_of_lt prime_gt_one)
      (nat.succ_le_iff.2 (succ_pos _))) (nat.succ_le_iff.2 (fact.out _)),
    { assumption, }, },
  rw [←zmod.nat_cast_val, zmod.val_mul, nat.mod_eq_of_lt _, nat.cast_mul],
  { apply congr_arg2,
    { rw [cast_val_eq_of_le _ le_mul_p, int.nat_cast_eq_coe_nat, _root_.coe_coe], },
    { rw [zmod.val_mul, nat.mod_eq_of_lt _],
      { rw [nat.cast_mul, zmod.nat_cast_val, zmod.nat_cast_val, ←nat.cast_pow],
        apply congr_arg2 _ rfl _,
        by_cases m = 0,
        { rw [h, pow_zero, pow_zero, nat.cast_one],
          haveI : fact (1 < d * p^1),
          { apply fact_iff.2 (one_lt_mul (nat.succ_le_iff.2 (fact.out _)) _),
            { assumption, },
            { rw pow_one p, assumption, }, },
          apply cast_int_one, },
        { rw [nat_cast_zmod_cast_int (lt_mul_pow_right (fact.out _) prime_gt_one
            (nat.succ_lt_succ (nat.pos_of_ne_zero h))), nat_cast_zmod_cast_int
            (pow_lt_mul_pow_succ_right _), int.coe_nat_pow],
          any_goals { assumption, }, }, },
      { rw [←nat.cast_pow, zmod.val_cast_of_lt _, zmod.val_cast_of_lt (pow_lt_mul_pow_succ_right _)],
        apply mul_pow_lt_mul_pow_succ,
        any_goals { assumption, },
        { apply lt_mul_of_one_lt_right (fact.out _) (nat.one_lt_pow _ _ (nat.succ_pos _)
            (nat.prime.one_lt (fact.out _))),
          any_goals { assumption }, }, }, }, },
  { rw [←nat.cast_pow, ←nat.cast_mul, zmod.val_cast_of_lt (mul_pow_lt_mul_pow_succ _),
      cast_val_eq_of_le _ le_mul_p],
    { apply fin_prime_mul_prime_pow_lt_mul_prime_pow_succ, },
    any_goals { assumption, }, },
end

-- should p be implicit or explicit?
variables {p d}
theorem sum_fract [fact (0 < d)] {m : ℕ} (x : zmod (d * p^m)) :
  ∑ (x_1 : (equi_class m.succ x)), int.fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) /
    ((d : ℚ) * (p : ℚ)^m.succ)) = (x.val : ℚ) / (d * p^m) + (p - 1) / 2 :=
begin
  conv_lhs { congr, skip, funext, rw [← nat.cast_pow, ← nat.cast_mul,
    int.fract_eq_self' ((zero_le_div_and_div_lt_one (x_1 : zmod (d * p ^ m.succ))).1)
    ((zero_le_div_and_div_lt_one (x_1 : zmod (d * p ^ m.succ))).2),  nat.cast_mul, nat.cast_pow], },
  rw fintype.sum_equiv (equi_iso_fin m x) (λ y, _)
    (λ k, (((equi_iso_fin m x).inv_fun k).val : ℚ) / (d * p ^ m.succ)),
  { rw ←finset.sum_div,
    have h1 : ∀ y : fin p, ((x.val : zmod (d * p^m.succ)) : ℤ) + ↑((y : zmod (d * p^m.succ)) *
      (d * p ^ m : zmod (d * p^m.succ))) < ↑(d * p ^ m.succ : ℕ),
    { intro y,
      rw [zmod.nat_cast_val, ←zmod.nat_cast_val, ←zmod.nat_cast_val (↑y * (_ * _)), ←nat.cast_add],
      { convert (int.coe_nat_lt).2 (val_add_fin_mul_lt x y) using 1,
        apply congr (funext int.nat_cast_eq_coe_nat) (congr_arg2 _ _ _),
        { rw [←zmod.nat_cast_val, coe_val_eq_val_of_lt (mul_pow_lt_mul_pow_succ _) _],
          any_goals { apply_instance, }, },
        { rw [←nat.cast_pow, ←nat.cast_mul, fin_prime_coe_coe, ←nat.cast_mul, zmod.val_cast_of_lt],
          apply fin_prime_mul_prime_pow_lt_mul_prime_pow_succ, }, },
      { apply_instance, }, },
    conv_lhs { congr, congr, skip, funext, rw [equi_iso_fun_inv_val, ←zmod.int_cast_cast,
      coe_add_eq_pos' (h1 _), int.cast_add, helper_2 p d m _], },
    { rw [finset.sum_add_distrib, finset.sum_const, finset.card_univ, fintype.card_fin _],
      norm_cast,
      rw [←finset.sum_mul, _root_.add_div],
      apply congr_arg2 _ ((div_eq_iff _).2 _) _,
      { norm_cast, apply ne_of_gt (fact_iff.1 _), apply_instance, apply_instance, },
      { rw [div_mul_comm, _root_.nsmul_eq_mul],
        apply congr_arg2 _ _ _,
        { norm_num,
          rw [mul_div_mul_left _, pow_succ, mul_div_cancel _],
          { norm_cast,
            apply pow_ne_zero m (nat.prime.ne_zero (fact_iff.1 _)), assumption, },
          { norm_num,
            apply ne_of_gt (fact_iff.1 infer_instance), apply_instance, assumption, }, },
        { rw [zmod.int_cast_cast, zmod.nat_cast_val, ←zmod.nat_cast_val (x : zmod (d * p^m.succ))],
          refine congr_arg _ _,
          rw [←zmod.nat_cast_val x, coe_val_eq_val_of_lt _ _],
          { apply_instance, },
          { rw [mul_comm d (p^m), mul_comm d (p^m.succ)],
            apply mul_lt_mul (pow_lt_pow (nat.prime.one_lt (fact_iff.1 _)) (nat.lt_succ_self m))
              le_rfl (fact.out _) (nat.zero_le _),
            any_goals { assumption, }, }, }, },
      { rw [int.cast_mul, mul_div_assoc, sum_rat_fin, nat.cast_mul, int.cast_mul],
        have one : ((p : ℚ) - 1) * (p : ℚ) / 2 * (1 / (p : ℚ)) = ((p : ℚ) - 1) / 2,
        { rw [_root_.div_mul_div_comm, mul_one, mul_div_mul_right],
          norm_cast, apply ne_of_gt (nat.prime.pos (fact_iff.1 _)), assumption, },
        convert one using 2,
        rw div_eq_div_iff _ _,
        { rw [one_mul, zmod.int_cast_cast, int.cast_pow, zmod.int_cast_cast, pow_succ',
            nat.cast_mul, nat.cast_pow, mul_assoc],
          apply congr_arg2 _ _ _,
          { rw ←zmod.nat_cast_val _,
            { rw zmod.val_nat_cast,
              apply congr_arg _ (nat.mod_eq_of_lt ((lt_mul_iff_one_lt_right (fact_iff.1 _)).2 _)),
              { assumption, },
              { rw ←pow_succ',
                apply _root_.one_lt_pow (nat.prime.one_lt (fact_iff.1 _)) (succ_ne_zero _),
                { assumption, }, }, },
            { rw ←pow_succ', apply_instance, } },
          { apply congr_arg2 _ _ rfl,
            { by_cases m = 0,
              { rw [h, pow_zero, pow_zero], },
              apply congr_arg2 _ _ rfl,
              { rw ←zmod.nat_cast_val _,
                { rw zmod.val_nat_cast,
                  apply congr_arg _ (nat.mod_eq_of_lt _),
                  rw [←mul_assoc, lt_mul_iff_one_lt_left (prime.pos (fact_iff.1 _))],
                  { apply one_lt_mul (nat.succ_le_iff.2 (fact_iff.1 _)) _,
                    { assumption, },
                    { apply _root_.one_lt_pow (nat.prime.one_lt (fact_iff.1 _)) h,
                      assumption, }, },
                  { assumption, }, },
                { rw ←pow_succ', apply_instance, }, }, }, }, },
        { rw ←nat.cast_mul, norm_cast,
          apply ne_of_gt (fact_iff.1 _), apply_instance, apply_instance, },
        { norm_cast, apply ne_of_gt (nat.prime.pos (fact_iff.1 _)), assumption, }, }, }, },
  { rintros y,
    simp only [equiv.symm_apply_apply, subtype.val_eq_coe, equiv.inv_fun_as_coe,
      zmod.nat_cast_val], },
end
-- break up into smaller pieces

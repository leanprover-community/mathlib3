/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import ring_theory.polynomial.cyclotomic.basic
import tactic.by_contra
import topology.algebra.polynomial
import number_theory.padics.padic_val
import analysis.complex.arg

/-!
# Evaluating cyclotomic polynomials
This file states some results about evaluating cyclotomic polynomials in various different ways.
## Main definitions
* `polynomial.eval(₂)_one_cyclotomic_prime(_pow)`: `eval 1 (cyclotomic p^k R) = p`.
* `polynomial.eval_one_cyclotomic_not_prime_pow`: Otherwise, `eval 1 (cyclotomic n R) = 1`.
* `polynomial.cyclotomic_pos` : `∀ x, 0 < eval x (cyclotomic n R)` if `2 < n`.
-/

namespace polynomial

open finset nat
open_locale big_operators

@[simp] lemma eval_one_cyclotomic_prime {R : Type*} [comm_ring R] {p : ℕ} [hn : fact p.prime] :
  eval 1 (cyclotomic p R) = p :=
by simp only [cyclotomic_eq_geom_sum hn.out, eval_X, one_pow, sum_const, eval_pow,
              eval_finset_sum, card_range, smul_one_eq_coe]

@[simp] lemma eval₂_one_cyclotomic_prime {R S : Type*} [comm_ring R] [semiring S] (f : R →+* S)
  {p : ℕ} [fact p.prime] : eval₂ f 1 (cyclotomic p R) = p :=
by simp

@[simp] lemma eval_one_cyclotomic_prime_pow {R : Type*} [comm_ring R] {p : ℕ} (k : ℕ)
  [hn : fact p.prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p :=
by simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, eval_X, one_pow, sum_const,
              eval_pow, eval_finset_sum, card_range, smul_one_eq_coe]

@[simp] lemma eval₂_one_cyclotomic_prime_pow {R S : Type*} [comm_ring R] [semiring S] (f : R →+* S)
  {p : ℕ} (k : ℕ) [fact p.prime] : eval₂ f 1 (cyclotomic (p ^ (k + 1)) R) = p :=
by simp

private lemma cyclotomic_neg_one_pos {n : ℕ} (hn : 2 < n) {R} [linear_ordered_comm_ring R] :
  0 < eval (-1 : R) (cyclotomic n R) :=
begin
  haveI := ne_zero.of_gt hn,
  rw [←map_cyclotomic_int, ←int.cast_one, ←int.cast_neg, eval_int_cast_map,
      int.coe_cast_ring_hom, int.cast_pos],
  suffices : 0 < eval ↑(-1 : ℤ) (cyclotomic n ℝ),
  { rw [←map_cyclotomic_int n ℝ, eval_int_cast_map, int.coe_cast_ring_hom] at this,
    exact_mod_cast this },
  simp only [int.cast_one, int.cast_neg],
  have h0 := cyclotomic_coeff_zero ℝ hn.le,
  rw coeff_zero_eq_eval_zero at h0,
  by_contra' hx,
  have := intermediate_value_univ (-1) 0 (cyclotomic n ℝ).continuous,
  obtain ⟨y, hy : is_root _ y⟩ := this (show (0 : ℝ) ∈ set.Icc _ _, by simpa [h0] using hx),
  rw is_root_cyclotomic_iff at hy,
  rw hy.eq_order_of at hn,
  exact hn.not_le linear_ordered_ring.order_of_le_two,
end

lemma cyclotomic_pos {n : ℕ} (hn : 2 < n) {R} [linear_ordered_comm_ring R] (x : R) :
  0 < eval x (cyclotomic n R) :=
begin
  induction n using nat.strong_induction_on with n ih,
  have hn'  : 0 < n := pos_of_gt hn,
  have hn'' : 1 < n := one_lt_two.trans hn,
  dsimp at ih,
  have := prod_cyclotomic_eq_geom_sum hn' R,
  apply_fun eval x at this,
  rw [divisors_eq_proper_divisors_insert_self_of_pos hn', insert_sdiff_of_not_mem,
      prod_insert, eval_mul, eval_geom_sum] at this,
  rotate,
  { simp only [lt_self_iff_false, mem_sdiff, not_false_iff, mem_proper_divisors, and_false,
      false_and]},
  { simpa only [mem_singleton] using hn''.ne' },
  rcases lt_trichotomy 0 (∑ i in range n, x ^ i) with h | h | h,
  { apply pos_of_mul_pos_right,
    { rwa this },
    rw eval_prod,
    refine prod_nonneg (λ i hi, _),
    simp only [mem_sdiff, mem_proper_divisors, mem_singleton] at hi,
    rw geom_sum_pos_iff hn'' at h,
    cases h with hk hx,
    { refine (ih _ hi.1.2 (nat.two_lt_of_ne _ hi.2 _)).le; rintro rfl,
      { exact hn'.ne' (zero_dvd_iff.mp hi.1.1) },
      { exact even_iff_not_odd.mp (even_iff_two_dvd.mpr hi.1.1) hk } },
    { rcases eq_or_ne i 2 with rfl | hk,
      { simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using hx.le },
      refine (ih _ hi.1.2 (nat.two_lt_of_ne _ hi.2 hk)).le,
      rintro rfl,
      exact (hn'.ne' $ zero_dvd_iff.mp hi.1.1) } },
  { rw [eq_comm, geom_sum_eq_zero_iff_neg_one hn''] at h,
    exact h.1.symm ▸ cyclotomic_neg_one_pos hn },
  { apply pos_of_mul_neg_left,
    { rwa this },
    rw [geom_sum_neg_iff hn''] at h,
    have h2 : {2} ⊆ n.proper_divisors \ {1},
    { rw [singleton_subset_iff, mem_sdiff, mem_proper_divisors, not_mem_singleton],
      exact ⟨⟨even_iff_two_dvd.mp h.1, hn⟩, (nat.one_lt_bit0 one_ne_zero).ne'⟩ },
    rw [eval_prod, ←prod_sdiff h2, prod_singleton]; try { apply_instance },
    apply mul_nonpos_of_nonneg_of_nonpos,
    { refine prod_nonneg (λ i hi, le_of_lt _),
      simp only [mem_sdiff, mem_proper_divisors, mem_singleton] at hi,
      refine ih _ hi.1.1.2 (nat.two_lt_of_ne _ hi.1.2 hi.2),
      rintro rfl,
      rw zero_dvd_iff at hi,
      exact hn'.ne' hi.1.1.1 },
    { simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using h.right.le } }
end

lemma cyclotomic_pos_and_nonneg (n : ℕ) {R} [linear_ordered_comm_ring R] (x : R) :
  (1 < x → 0 < eval x (cyclotomic n R)) ∧ (1 ≤ x → 0 ≤ eval x (cyclotomic n R)) :=
begin
  rcases n with _ | _ | _ | n;
  simp only [cyclotomic_zero, cyclotomic_one, cyclotomic_two, succ_eq_add_one,
    eval_X, eval_one, eval_add, eval_sub, sub_nonneg, sub_pos,
    zero_lt_one, zero_le_one, implies_true_iff, imp_self, and_self],
  { split; intro; linarith, },
  { have : 2 < n + 3 := dec_trivial,
    split; intro; [skip, apply le_of_lt]; apply cyclotomic_pos this, },
end

/-- Cyclotomic polynomials are always positive on inputs larger than one.
Similar to `cyclotomic_pos` but with the condition on the input rather than index of the
cyclotomic polynomial. -/
lemma cyclotomic_pos' (n : ℕ) {R} [linear_ordered_comm_ring R] {x : R} (hx : 1 < x) :
  0 < eval x (cyclotomic n R) :=
(cyclotomic_pos_and_nonneg n x).1 hx

/-- Cyclotomic polynomials are always nonnegative on inputs one or more. -/
lemma cyclotomic_nonneg (n : ℕ) {R} [linear_ordered_comm_ring R] {x : R} (hx : 1 ≤ x) :
  0 ≤ eval x (cyclotomic n R) :=
(cyclotomic_pos_and_nonneg n x).2 hx

lemma eval_one_cyclotomic_not_prime_pow {R : Type*} [comm_ring R] {n : ℕ}
  (h : ∀ {p : ℕ}, p.prime → ∀ k : ℕ, p ^ k ≠ n) : eval 1 (cyclotomic n R) = 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn',
  { simp },
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h nat.prime_two 0).symm⟩,
  suffices : eval 1 (cyclotomic n ℤ) = 1 ∨ eval 1 (cyclotomic n ℤ) = -1,
  { cases this with h h,
    { have := eval_int_cast_map (int.cast_ring_hom R) (cyclotomic n ℤ) 1,
      simpa only [map_cyclotomic, int.cast_one, h, ring_hom.eq_int_cast] using this },
    { exfalso,
      linarith [cyclotomic_nonneg n (le_refl (1 : ℤ))] }, },
  rw [←int.nat_abs_eq_nat_abs_iff, int.nat_abs_one, nat.eq_one_iff_not_exists_prime_dvd],
  intros p hp hpe,
  haveI := fact.mk hp,

  have hpn : p ∣ n,
  { apply hpe.trans,
    nth_rewrite 1 ←int.nat_abs_of_nat n,
    rw [int.nat_abs_dvd_iff_dvd, ←int.nat_cast_eq_coe_nat,
        ←one_geom_sum, ←eval_geom_sum, ←prod_cyclotomic_eq_geom_sum hn'],
    apply eval_dvd,
    apply finset.dvd_prod_of_mem,
    simpa using and.intro hn'.ne' hn.ne' },

  have := prod_cyclotomic_eq_geom_sum hn' ℤ,
  apply_fun eval 1 at this,
  rw [eval_geom_sum, one_geom_sum, eval_prod, eq_comm,
      ←finset.prod_sdiff $ range_pow_padic_val_nat_subset_divisors' p, finset.prod_image] at this,
  simp_rw [eval_one_cyclotomic_prime_pow, finset.prod_const, finset.card_range, mul_comm] at this,
  rw [←finset.prod_sdiff $ show {n} ⊆ _, from _] at this,
  any_goals {apply_instance},
  swap,
  { simp only [not_exists, true_and, exists_prop, dvd_rfl, finset.mem_image, finset.mem_range,
    finset.mem_singleton, finset.singleton_subset_iff, finset.mem_sdiff, nat.mem_divisors, not_and],
    exact ⟨⟨hn'.ne', hn.ne'⟩, λ t _, h hp _⟩ },
  rw [←int.nat_abs_of_nat p, int.nat_abs_dvd_iff_dvd] at hpe,
  obtain ⟨t, ht⟩ := hpe,
  rw [finset.prod_singleton, ht, mul_left_comm, mul_comm, ←mul_assoc, mul_assoc] at this,
  simp only [int.nat_cast_eq_coe_nat] at *,
  have : (p ^ (padic_val_nat p n) * p : ℤ) ∣ n := ⟨_, this⟩,
  simp only [←pow_succ', ←int.nat_abs_dvd_iff_dvd, int.nat_abs_of_nat, int.nat_abs_pow] at this,
  exact pow_succ_padic_val_nat_not_dvd hn' this,
  { rintro x - y - hxy,
    apply nat.succ_injective,
    exact nat.pow_right_injective hp.two_le hxy }
end

lemma sub_one_pow_totient_lt_cyclotomic_eval {n : ℕ} {q : ℝ} (hn' : 2 ≤ n) (hq' : 1 < q) :
  (q - 1) ^ totient n < (cyclotomic n ℝ).eval q :=
begin
  have hn : 0 < n := pos_of_gt hn',
  have hq := zero_lt_one.trans hq',
  have hfor : ∀ ζ' ∈ primitive_roots n ℂ, q - 1 ≤ ∥↑q - ζ'∥,
  { intros ζ' hζ',
    rw mem_primitive_roots hn at hζ',
    convert norm_sub_norm_le (↑q) ζ',
    { rw [complex.norm_real, real.norm_of_nonneg hq.le], },
    { rw [hζ'.norm'_eq_one hn.ne'] } },
  let ζ := complex.exp (2 * ↑real.pi * complex.I / ↑n),
  have hζ : is_primitive_root ζ n := complex.is_primitive_root_exp n hn.ne',
  have hex : ∃ ζ' ∈ primitive_roots n ℂ, q - 1 < ∥↑q - ζ'∥,
  { refine ⟨ζ, (mem_primitive_roots hn).mpr hζ, _⟩,
    suffices : ¬ same_ray ℝ (q : ℂ) ζ,
    { convert lt_norm_sub_of_not_same_ray this;
      simp [real.norm_of_nonneg hq.le, hζ.norm'_eq_one hn.ne'] },
    rw complex.same_ray_iff,
    push_neg,
    refine ⟨by exact_mod_cast hq.ne', hζ.ne_zero hn.ne', _⟩,
    rw [complex.arg_of_real_of_nonneg hq.le, ne.def, eq_comm, hζ.arg_eq_zero_iff hn.ne'],
    clear_value ζ,
    rintro rfl,
    linarith [hζ.unique is_primitive_root.one] },
  have : ¬eval ↑q (cyclotomic n ℂ) = 0,
  { erw cyclotomic.eval_apply q n (algebra_map ℝ ℂ),
    simpa using (cyclotomic_pos' n hq').ne' },
  suffices : (units.mk0 (real.to_nnreal (q - 1)) (by simp [hq'])) ^ totient n
              < units.mk0 (∥(cyclotomic n ℂ).eval q∥₊) (by simp [this]),
  { simp only [←units.coe_lt_coe, units.coe_pow, units.coe_mk0, ← nnreal.coe_lt_coe, hq'.le,
               real.to_nnreal_lt_to_nnreal_iff_of_nonneg, coe_nnnorm, complex.norm_eq_abs,
               nnreal.coe_pow, real.coe_to_nnreal', max_eq_left, sub_nonneg] at this,
    convert this,
    erw [(cyclotomic.eval_apply q n (algebra_map ℝ ℂ)), eq_comm],
    simp [cyclotomic_nonneg n hq'.le], },
  simp only [cyclotomic_eq_prod_X_sub_primitive_roots hζ, eval_prod, eval_C,
             eval_X, eval_sub, nnnorm_prod, units.mk0_prod],
  convert prod_lt_prod' _ _,
  swap, { exact λ _, units.mk0 (real.to_nnreal (q - 1)) (by simp [hq']) },
  { simp [complex.card_primitive_roots] },
  { simp only [subtype.coe_mk, mem_attach, forall_true_left, subtype.forall, ←units.coe_le_coe,
      ← nnreal.coe_le_coe, complex.abs_nonneg, hq'.le, units.coe_mk0, real.coe_to_nnreal',
      coe_nnnorm, complex.norm_eq_abs, max_le_iff, tsub_le_iff_right],
    intros x hx,
    simpa using hfor x hx, },
  { simp only [subtype.coe_mk, mem_attach, exists_true_left, subtype.exists,
      ← nnreal.coe_lt_coe, ← units.coe_lt_coe, units.coe_mk0 _, coe_nnnorm],
    simpa [hq'.le] using hex, },
end

lemma cyclotomic_eval_lt_sub_one_pow_totient {n : ℕ} {q : ℝ} (hn' : 3 ≤ n) (hq' : 1 < q) :
  (cyclotomic n ℝ).eval q < (q + 1) ^ totient n :=
begin
  have hn : 0 < n := pos_of_gt hn',
  have hq := zero_lt_one.trans hq',
  have hfor : ∀ ζ' ∈ primitive_roots n ℂ, ∥↑q - ζ'∥ ≤ q + 1,
  { intros ζ' hζ',
    rw mem_primitive_roots hn at hζ',
    convert norm_sub_le (↑q) ζ',
    { rw [complex.norm_real, real.norm_of_nonneg (zero_le_one.trans_lt hq').le], },
    { rw [hζ'.norm'_eq_one hn.ne'] }, },
  let ζ := complex.exp (2 * ↑real.pi * complex.I / ↑n),
  have hζ : is_primitive_root ζ n := complex.is_primitive_root_exp n hn.ne',
  have hex : ∃ ζ' ∈ primitive_roots n ℂ, ∥↑q - ζ'∥ < q + 1,
  { refine ⟨ζ, (mem_primitive_roots hn).mpr hζ, _⟩,
    suffices : ¬ same_ray ℝ (q : ℂ) (-ζ),
    { convert norm_add_lt_of_not_same_ray this;
      simp [real.norm_of_nonneg hq.le, hζ.norm'_eq_one hn.ne', -complex.norm_eq_abs] },
    rw complex.same_ray_iff,
    push_neg,
    refine ⟨by exact_mod_cast hq.ne', neg_ne_zero.mpr $ hζ.ne_zero hn.ne', _⟩,
    rw [complex.arg_of_real_of_nonneg hq.le, ne.def, eq_comm],
    intro h,
    rw [complex.arg_eq_zero_iff, complex.neg_re, neg_nonneg, complex.neg_im, neg_eq_zero] at h,
    have hζ₀ : ζ ≠ 0,
    { clear_value ζ,
      rintro rfl,
      exact hn.ne' (hζ.unique is_primitive_root.zero) },
    have : ζ.re < 0 ∧ ζ.im = 0 := ⟨h.1.lt_of_ne _, h.2⟩,
    rw [←complex.arg_eq_pi_iff, hζ.arg_eq_pi_iff hn.ne'] at this,
    rw this at hζ,
    linarith [hζ.unique $ is_primitive_root.neg_one 0 two_ne_zero.symm],
    { contrapose! hζ₀,
      ext; simp [hζ₀, h.2] } },
  have : ¬eval ↑q (cyclotomic n ℂ) = 0,
  { erw cyclotomic.eval_apply q n (algebra_map ℝ ℂ),
    simp only [complex.coe_algebra_map, complex.of_real_eq_zero],
    exact (cyclotomic_pos' n hq').ne.symm, },
  suffices : units.mk0 (∥(cyclotomic n ℂ).eval q∥₊) (by simp [this])
           < (units.mk0 (real.to_nnreal (q + 1)) (by simp; linarith)) ^ totient n,
  { simp only [←units.coe_lt_coe, units.coe_pow, units.coe_mk0, ← nnreal.coe_lt_coe, hq'.le,
               real.to_nnreal_lt_to_nnreal_iff_of_nonneg, coe_nnnorm, complex.norm_eq_abs,
               nnreal.coe_pow, real.coe_to_nnreal', max_eq_left, sub_nonneg] at this,
    convert this,
    { erw [(cyclotomic.eval_apply q n (algebra_map ℝ ℂ)), eq_comm],
      simp [cyclotomic_nonneg n hq'.le] },
    rw [eq_comm, max_eq_left_iff],
    linarith },
  simp only [cyclotomic_eq_prod_X_sub_primitive_roots hζ, eval_prod, eval_C,
             eval_X, eval_sub, nnnorm_prod, units.mk0_prod],
  convert prod_lt_prod' _ _,
  swap, { exact λ _, units.mk0 (real.to_nnreal (q + 1)) (by simp; linarith only [hq']) },
  { simp [complex.card_primitive_roots], },
  { simp only [subtype.coe_mk, mem_attach, forall_true_left, subtype.forall, ←units.coe_le_coe,
      ← nnreal.coe_le_coe, complex.abs_nonneg, hq'.le, units.coe_mk0, real.coe_to_nnreal,
      coe_nnnorm, complex.norm_eq_abs, max_le_iff],
    intros x hx,
    have : complex.abs _ ≤ _ := hfor x hx,
    simp [this], },
  { simp only [subtype.coe_mk, mem_attach, exists_true_left, subtype.exists,
      ← nnreal.coe_lt_coe, ← units.coe_lt_coe, units.coe_mk0 _, coe_nnnorm],
    obtain ⟨ζ, hζ, hhζ : complex.abs _ < _⟩ := hex,
    exact ⟨ζ, hζ, by simp [hhζ]⟩ },
end

lemma sub_one_lt_nat_abs_cyclotomic_eval {n : ℕ} {q : ℕ} (hn' : 1 < n) (hq' : q ≠ 1) :
  q - 1 < ((cyclotomic n ℤ).eval ↑q).nat_abs :=
begin
  rcases q with _ | _ | q,
  iterate 2
  { rw [pos_iff_ne_zero, ne.def, int.nat_abs_eq_zero],
    intro h,
    have := degree_eq_one_of_irreducible_of_root (cyclotomic.irreducible (pos_of_gt hn')) h,
    rw [degree_cyclotomic, with_top.coe_eq_one, totient_eq_one_iff] at this,
    rcases this with rfl|rfl; simpa using h },
  suffices : (q.succ : ℝ) < (eval (↑q + 1 + 1) (cyclotomic n ℤ)).nat_abs,
  { exact_mod_cast this },
  calc _ ≤ ((q + 2 - 1) ^ n.totient : ℝ) : _
    ...  < _ : _,
  { norm_num,
    convert pow_mono (by simp : 1 ≤ (q : ℝ) + 1) (totient_pos (pos_of_gt hn') : 1 ≤ n.totient),
    { simp },
    { ring }, },
  convert sub_one_pow_totient_lt_cyclotomic_eval (show 2 ≤ n, by linarith)
                          (show (1 : ℝ) < q + 2, by {norm_cast, linarith}),
  norm_cast,
  erw cyclotomic.eval_apply (q + 2 : ℤ) n (algebra_map ℤ ℝ),
  simp only [int.coe_nat_succ, ring_hom.eq_int_cast],
  norm_cast,
  rw [int.coe_nat_abs_eq_normalize, int.normalize_of_nonneg],
  simp only [int.coe_nat_succ],
  exact cyclotomic_nonneg n (by linarith),
end

end polynomial

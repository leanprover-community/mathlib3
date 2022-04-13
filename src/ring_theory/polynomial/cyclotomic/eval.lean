/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import ring_theory.polynomial.cyclotomic.basic
import tactic.by_contra
import topology.algebra.polynomial
import number_theory.padics.padic_norm
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
by simp only [cyclotomic_eq_geom_sum hn.out, geom_sum_def, eval_X, one_pow, sum_const, eval_pow,
              eval_finset_sum, card_range, smul_one_eq_coe]

@[simp] lemma eval₂_one_cyclotomic_prime {R S : Type*} [comm_ring R] [semiring S] (f : R →+* S)
  {p : ℕ} [fact p.prime] : eval₂ f 1 (cyclotomic p R) = p :=
by simp

@[simp] lemma eval_one_cyclotomic_prime_pow {R : Type*} [comm_ring R] {p : ℕ} (k : ℕ)
  [hn : fact p.prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p :=
by simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_def, eval_X, one_pow, sum_const,
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
  rcases lt_trichotomy 0 (geom_sum x n) with h | h | h,
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

open_locale complex_conjugate nnreal

section is_R_or_C
open is_R_or_C

lemma eq_neg_iff {R : Type*} [ring R] [invertible (2 : R)] (x : R) :
  x = -x ↔ x = 0 :=
begin
  have : is_unit (⅟ (2:R)) := is_unit_of_invertible _,
  rw [eq_neg_iff_add_eq_zero, ← two_mul, ← this.mul_right_inj, inv_of_mul_self_assoc, mul_zero],
end

lemma conj_eq_neg_iff {K : Type*} [is_R_or_C K] (z : K) :
  conj z = -z ↔ re z = 0 :=
begin
  rw [← re_add_im z, ring_hom.map_add, ring_hom.map_mul, conj_of_real, conj_of_real, conj_I,
      neg_add, re_add_im, mul_neg, add_left_inj, eq_neg_iff, of_real_eq_zero],
end
end is_R_or_C

@[simp]
lemma conj_exp_primitive_root (n : ℕ) : conj (complex.exp (2 * ↑real.pi * complex.I / ↑n)) =
                                        complex.exp (- (2 * ↑real.pi * complex.I / ↑n)) :=
begin
  rw ← complex.exp_conj,
  congr,
  simp only [div_eq_mul_inv, is_R_or_C.re_to_complex, complex.mul_re, complex.bit0_im, complex.I_re,
             complex.one_im, bit0_zero, complex.of_real_im, mul_zero, sub_zero, conj_eq_neg_iff,
             complex.mul_im, zero_mul, add_zero, complex.inv_im, complex.nat_cast_im, neg_zero],
end

lemma units.mk0_prod {β α : Type} [_inst_1 : comm_group_with_zero β] (s : finset α)
  (f : α → β) (h) :
  units.mk0 (∏ b in s, f b) h = ∏ b in s.attach, units.mk0 (f b) (λ hh, h (prod_eq_zero b.2 hh)) :=
begin
  classical,
  induction s using finset.induction_on with x si hsi hi; simp*
end

lemma cyclotomic.eval_apply {C R : Type*} (q : R) (n : ℕ) [ring C] [ring R] (f : R →+* C) :
  eval (f q) (cyclotomic n C) = f (eval q (cyclotomic n R)) :=
by rw [← map_cyclotomic n f, eval_map, eval₂_at_apply]

lemma _root_.is_primitive_root.ne_zero {M} [comm_monoid_with_zero M] [nontrivial M] {ζ : M} {n : ℕ}
  (h : is_primitive_root ζ n) : n ≠ 0 → ζ ≠ 0 :=
mt $ λ hn, h.unique (hn.symm ▸ is_primitive_root.zero)

lemma _root_.mul_rotate  {S} [comm_semigroup S] (a b c : S) : a * b * c = b * c * a :=
by simp only [mul_left_comm, mul_comm]
lemma _root_.mul_rotate' {S} [comm_semigroup S] (a b c : S) : a * (b * c) = b * (c * a) :=
by simp only [mul_left_comm, mul_comm]

lemma _root_.add_one_mul {R} [non_assoc_semiring R] (a b : R) : a * b + b = (a + 1) * b :=
by rw [add_mul, one_mul]
lemma _root_.sub_one_mul {R} [non_assoc_ring R] (a b : R) : a * b - b = (a - 1) * b :=
by rw [sub_mul, one_mul]
lemma _root_.mul_add_one {R} [non_assoc_semiring R] (a b : R) : a * b + a = a * (b + 1) :=
by rw [mul_add, mul_one]
lemma _root_.mul_sub_one {R} [non_assoc_ring R] (a b : R) : a * b - a = a * (b - 1) :=
by rw [mul_sub, mul_one]

lemma _root_.is_primitive_root.arg {n : ℕ} {ζ : ℂ} (h : is_primitive_root ζ n) (hn : n ≠ 0) :
  ∃ i : ℤ, ζ.arg = i / n * (2 * real.pi) ∧ is_coprime i n ∧ i.nat_abs < n :=
begin
  rw complex.is_primitive_root_iff _ _ hn at h,
  obtain ⟨i, h, hin, rfl⟩ := h,
  rw [mul_comm, ←mul_assoc, complex.exp_mul_I],
  refine ⟨if i * 2 ≤ n then i else i - n, _, _, _⟩,
  work_on_goal 2
  { replace hin := nat.is_coprime_iff_coprime.mpr hin,
    split_ifs with _,
    { exact hin },
    { convert hin.add_mul_left_left (-1),
      rw [mul_neg_one, sub_eq_add_neg] } },
  work_on_goal 2
  { split_ifs with h₂,
    { exact_mod_cast h },
    suffices : (i - n : ℤ).nat_abs = n - i,
    { rw this,
      apply tsub_lt_self hn.bot_lt,
      contrapose! h₂,
      rw [nat.eq_zero_of_le_zero h₂, zero_mul],
      exact zero_le _ },
    rw [←int.nat_abs_neg, neg_sub, int.nat_abs_eq_iff],
    exact or.inl (int.coe_nat_sub h.le).symm },
  split_ifs with h₂,
  { convert complex.arg_cos_add_sin_mul_I _,
    { push_cast },
    { push_cast },
    field_simp [hn],
    refine ⟨(neg_lt_neg real.pi_pos).trans_le _, _⟩,
    { rw neg_zero,
      exact mul_nonneg (mul_nonneg (cast_nonneg _) $ by simp [real.pi_pos.le]) (by simp) },
    rw [←mul_rotate', mul_div_assoc],
    rw ←mul_one n at h₂,
    exact mul_le_of_le_one_right real.pi_pos.le
      ((div_le_iff' $ by exact_mod_cast (pos_of_gt h)).mpr $ by exact_mod_cast h₂) },
  rw [←complex.cos_sub_two_pi, ←complex.sin_sub_two_pi],
  convert complex.arg_cos_add_sin_mul_I _,
  { push_cast,
    rw [sub_one_mul, sub_div, div_self],
    exact_mod_cast hn },
  { push_cast,
    rw [sub_one_mul, sub_div, div_self],
    exact_mod_cast hn },
  field_simp [hn],
  refine ⟨_, le_trans _ real.pi_pos.le⟩,
  work_on_goal 2
  { rw [mul_div_assoc],
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr $ by exact_mod_cast h.le)
      (div_nonneg (by simp [real.pi_pos.le]) $ by simp) },
  rw [←mul_rotate', mul_div_assoc, neg_lt, ←mul_neg, mul_lt_iff_lt_one_right real.pi_pos,
      ←neg_div, ←neg_mul, neg_sub, div_lt_iff, one_mul, sub_mul, sub_lt, mul_sub_one],
  norm_num,
  exact_mod_cast not_le.mp h₂,
  exact (cast_pos.mpr hn.bot_lt),
end

.

lemma _root_.is_primitive_root.arg_ne_zero {n : ℕ} {ζ : ℂ} (hζ : is_primitive_root ζ n)
  (hn : 1 < n) : ζ.arg ≠ 0 :=
begin
  obtain ⟨k, h, hin, hi⟩ := hζ.arg (pos_of_gt hn).ne',
  rw [h, ne.def, mul_eq_zero, _root_.div_eq_zero_iff, not_or_distrib, not_or_distrib],
  refine ⟨⟨_, _⟩, by linarith [real.pi_pos]⟩; norm_cast; rintro rfl,
  { rw [is_coprime_zero_left, int.is_unit_iff_nat_abs_eq, int.nat_abs_of_nat] at hin,
    subst hin,
    exact lt_irrefl 1 hn },
  exact lt_irrefl 0 (zero_lt_one.trans hn),
end
lemma sub_one_pow_totient_lt_cyclotomic_eval (n : ℕ) (q : ℝ) (hn' : 2 ≤ n) (hq' : 1 < q) :
  (q - 1) ^ totient n < (cyclotomic n ℝ).eval q :=
begin
  have hn : 0 < n := pos_of_gt hn',
  have hq := zero_lt_one.trans hq',
  have hfor : ∀ ζ' ∈ primitive_roots n ℂ, q - 1 ≤ ∥↑q - ζ'∥,
  { intros ζ' hζ',
    rw mem_primitive_roots hn at hζ',
    convert norm_sub_norm_le (↑q) ζ',
    { rw [complex.norm_real, real.norm_of_nonneg hq.le], },
    { rw [hζ'.nnnorm_eq_one hn.ne'], }, },
  let ζ := complex.exp (2 * ↑real.pi * complex.I / ↑n),
  have hζ : is_primitive_root ζ n := complex.is_primitive_root_exp n hn.ne',
  have hex : ∃ ζ' ∈ primitive_roots n ℂ, q - 1 < ∥↑q - ζ'∥,
  { refine ⟨ζ, (mem_primitive_roots hn).mpr hζ, _⟩,
    suffices : ¬ same_ray ℝ (q : ℂ) ζ,
    { convert lt_norm_sub_of_not_same_ray this;
      simp [real.norm_of_nonneg hq.le, hζ.nnnorm_eq_one hn.ne'] },
    rw complex.same_ray_iff,
    push_neg,
    refine ⟨by exact_mod_cast hq.ne', hζ.ne_zero hn.ne', _⟩,
    rw [complex.arg_of_real_of_nonneg hq.le],
    exact (hζ.arg_ne_zero hn').symm },
  have : ¬eval ↑q (cyclotomic n ℂ) = 0, -- this is also a general lemma
  { erw cyclotomic.eval_apply q n (algebra_map ℝ ℂ),
    simp only [complex.coe_algebra_map, complex.of_real_eq_zero],
    exact (cyclotomic_pos' n hq').ne.symm, },
  suffices : (units.mk0 (real.to_nnreal (q - 1)) (by simp [hq'])) ^ totient n
              < units.mk0 (∥(cyclotomic n ℂ).eval q∥₊) (by simp [this]),
  { simp only [←units.coe_lt_coe, units.coe_pow, units.coe_mk0, ← nnreal.coe_lt_coe, hq'.le,
               real.to_nnreal_lt_to_nnreal_iff_of_nonneg, coe_nnnorm, complex.norm_eq_abs,
               nnreal.coe_pow, real.coe_to_nnreal', max_eq_left, sub_nonneg] at this,
    convert this,
    erw (cyclotomic.eval_apply q n (algebra_map ℝ ℂ)),
    symmetry,
    simp [cyclotomic_nonneg n hq'.le], },
  simp only [cyclotomic_eq_prod_X_sub_primitive_roots hζ, eval_prod, eval_C,
             eval_X, eval_sub, nnnorm_prod, units.mk0_prod],
  convert prod_lt_prod' _ _,
  swap, { exact λ _, units.mk0 (real.to_nnreal (q - 1)) (by simp [hq']) },
  { simp [complex.card_primitive_roots], }, -- TODO make this and card roots of unity a simp lemma
  { simp only [subtype.coe_mk, mem_attach, forall_true_left, subtype.forall, ←units.coe_le_coe,
      ← nnreal.coe_le_coe, complex.abs_nonneg, hq'.le, units.coe_mk0, real.coe_to_nnreal',
      coe_nnnorm, complex.norm_eq_abs, max_le_iff, tsub_le_iff_right],
    intros x hx,
    simpa using hfor x hx, },
  { simp only [subtype.coe_mk, mem_attach, exists_true_left, subtype.exists,
      ← nnreal.coe_lt_coe, ← units.coe_lt_coe, units.coe_mk0 _, coe_nnnorm],
    simpa [hq'.le] using hex, },
end

lemma cyclotomic_eval_lt_sub_one_pow_totient (n : ℕ) (q : ℝ) (hn' : 3 ≤ n) (hq' : 1 < q) :
  (cyclotomic n ℝ).eval q < (q + 1) ^ totient n :=
begin
  have hn : 0 < n := pos_of_gt hn',
  have hq := zero_lt_one.trans hq',
  have hfor : ∀ ζ' ∈ primitive_roots n ℂ, ∥↑q - ζ'∥ ≤ q + 1,
  { intros ζ' hζ',
    rw mem_primitive_roots hn at hζ',
    convert norm_sub_le (↑q) ζ',
    { rw [complex.norm_real, real.norm_of_nonneg (zero_le_one.trans_lt hq').le], },
    { rw [hζ'.nnnorm_eq_one hn.ne'], }, },
  let ζ := complex.exp (2 * ↑real.pi * complex.I / ↑n),
  have hζ : is_primitive_root ζ n := complex.is_primitive_root_exp n hn.ne',
  have hex : ∃ ζ' ∈ primitive_roots n ℂ, ∥↑q - ζ'∥ < q + 1,
  -- todo: when Yael gets the strictly convex stuff in master, this will be very easy
  -- (the triangle inequality will be strict as q and ζ are not in the `same_ray`)
  { rw ← mem_primitive_roots hn at hζ,
    refine ⟨ζ, hζ, (hfor ζ hζ).lt_of_ne (λ h, _)⟩,
    have : ∥↑q - ζ∥^2 = (q + 1)^2 := (congr_fun (congr_arg pow h) 2),
    apply_fun (coe : ℝ → ℂ) at this,
    rw [complex.norm_eq_abs, ← complex.norm_sq_eq_abs, complex.norm_sq_eq_conj_mul_self] at this,
    simp only [ζ, pow_two, mul_sub, sub_mul, mul_one, one_mul,
      complex.of_real_sub, complex.of_real_mul, complex.of_real_one, ring_hom.map_sub,
      is_R_or_C.conj_of_real, conj_exp_primitive_root] at this,
    rw [← complex.exp_add, add_left_neg, complex.exp_zero, ← sub_eq_zero] at this,
    push_cast at this,
    ring_nf at this,
    rw [mul_eq_zero, complex.of_real_eq_zero, ← add_sub_assoc, sub_eq_zero,
      ← div_eq_one_iff_eq (two_ne_zero' : (2 : ℂ) ≠ 0),
      (by ring : 2 * ↑real.pi * complex.I / ↑n = 2 * ↑real.pi / ↑n * complex.I), ← neg_mul] at this,
    simp only [(zero_lt_one.trans hq').ne.symm, or_false] at this,
    -- squeeze_simp adds field_notation TODO
    revert this,
    rw [← neg_add, neg_div],
    change -complex.cos (2 * ↑real.pi / ↑n) ≠ 1,
    norm_cast,
    rw neg_eq_iff_add_eq_zero,
    rw add_eq_zero_iff_eq_neg,
    intro h,
    have := real.sin_eq_zero_iff_cos_eq.mpr (or.inr h),
    revert this,
    rw real.sin_eq_zero_iff_of_lt_of_lt,
    { simp [hn.ne.symm, real.pi_ne_zero, not_or_distrib, _root_.div_eq_zero_iff, mul_eq_zero,
        bit0_eq_zero, one_ne_zero, or_self, cast_eq_zero, not_false_iff], },
    { transitivity (0 : ℝ),
      { linarith only [real.pi_pos], },
      { apply div_pos,
        linarith only [real.pi_pos, hn],
        exact_mod_cast hn, }, },
    { rw div_lt_iff,
      sorry,
      exact_mod_cast hn, }, }, --END TOFIX
  have : ¬eval ↑q (cyclotomic n ℂ) = 0, -- this is also a general lemma
  { erw cyclotomic.eval_apply q n (algebra_map ℝ ℂ),
    simp only [complex.coe_algebra_map, complex.of_real_eq_zero],
    exact (cyclotomic_pos' n hq').ne.symm, },
  suffices : units.mk0 (∥(cyclotomic n ℂ).eval q∥₊) (by simp [this])
           < (units.mk0 (real.to_nnreal (q + 1)) (by simp; linarith)) ^ totient n,
  { simp only [←units.coe_lt_coe, units.coe_pow, units.coe_mk0, ← nnreal.coe_lt_coe, hq'.le,
               real.to_nnreal_lt_to_nnreal_iff_of_nonneg, coe_nnnorm, complex.norm_eq_abs,
               nnreal.coe_pow, real.coe_to_nnreal', max_eq_left, sub_nonneg] at this,
    convert this,
    erw (cyclotomic.eval_apply q n (algebra_map ℝ ℂ)),
    symmetry,
    simp [cyclotomic_nonneg n hq'.le],
    symmetry,
    simp,
    linarith, },
  simp only [cyclotomic_eq_prod_X_sub_primitive_roots hζ, eval_prod, eval_C,
             eval_X, eval_sub, nnnorm_prod, units.mk0_prod],
  convert prod_lt_prod' _ _,
  swap, { exact λ _, units.mk0 (real.to_nnreal (q + 1)) (by simp; linarith only [hq']) },
  { simp [complex.card_primitive_roots], }, -- TODO make this and card roots of unity a simp lemma
  { simp only [subtype.coe_mk, mem_attach, forall_true_left, subtype.forall, ←units.coe_le_coe,
      ← nnreal.coe_le_coe, complex.abs_nonneg, hq'.le, units.coe_mk0, real.coe_to_nnreal,
      coe_nnnorm, complex.norm_eq_abs, max_le_iff],
    intros x hx,
    have := hfor x hx,
    simp at this,
    simp [this], },
  { simp only [subtype.coe_mk, mem_attach, exists_true_left, subtype.exists,
      ← nnreal.coe_lt_coe, ← units.coe_lt_coe, units.coe_mk0 _, coe_nnnorm],
    obtain ⟨ζ, hζ, hhζ⟩ := hex,
    refine ⟨ζ, hζ, _⟩,
    simp at hhζ,
    simp [hhζ], },
end

lemma nat.totient_eq_one_iff : ∀ {n : ℕ}, n.totient = 1 ↔ n = 1 ∨ n = 2
| 0 := by simp
| 1 := by simp
| 2 := by simp
| (n+3) :=
begin
  have : 3 ≤ n + 3 := le_add_self,
  have := totient_even this,
  simp only [succ_succ_ne_one, false_or],
  exact ⟨λ h, (not_even_one).elim $ by rwa ←h, by rintro ⟨⟩⟩,
end

lemma sub_one_lt_nat_abs_cyclotomic_eval (n : ℕ) (q : ℕ) (hn' : 1 < n) (hq' : q ≠ 1) :
  q - 1 < ((cyclotomic n ℤ).eval ↑q).nat_abs :=
begin
  rcases q with _ | _ | q,
  iterate 2
  { rw [pos_iff_ne_zero, ne.def, int.nat_abs_eq_zero],
    intro h,
    have := degree_eq_one_of_irreducible_of_root (cyclotomic.irreducible (pos_of_gt hn')) h,
    rw [degree_cyclotomic, with_top.coe_eq_one, nat.totient_eq_one_iff] at this,
    rcases this with rfl|rfl; simpa using h },
  suffices : (q.succ : ℝ) < (eval (↑q + 1 + 1) (cyclotomic n ℤ)).nat_abs,
  { exact_mod_cast this, },
  calc _ ≤ ((q + 2 - 1) ^ n.totient : ℝ) : _
    ...  < _ : _,
  { norm_num,
    convert pow_mono (by simp : 1 ≤ (q : ℝ) + 1) (totient_pos (pos_of_gt hn') : 1 ≤ n.totient),
    { simp, },
    { ring, }, },
  convert sub_one_pow_totient_lt_cyclotomic_eval n (q + 2) (by linarith) (by norm_cast; linarith),
  norm_cast,
  erw cyclotomic.eval_apply (q + 2 : ℤ) n (algebra_map ℤ ℝ),
  simp only [int.coe_nat_succ, ring_hom.eq_int_cast],
  norm_cast,
  rw [int.coe_nat_abs_eq_normalize, int.normalize_of_nonneg],
  simp only [int.coe_nat_succ],
  exact cyclotomic_nonneg n (by linarith),
end

end polynomial

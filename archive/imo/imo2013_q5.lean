/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import algebra.geom_sum
import data.rat.basic
import data.real.basic

/-!
# IMO 2013 Q5

Let `ℚ>₀` be the positive rational numbers. Let `f : ℚ>₀ → ℝ` be a function satisfying
the conditions

1. `f(x) * f(y) ≥ f(x * y)`
2. `f(x + y) ≥ f(x) + f(y)`

for all `x, y ∈ ℚ>₀`. Given that `f(a) = a` for some rational `a > 1`, prove that `f(x) = x` for
all `x ∈ ℚ>₀`.

# Solution

We provide a direct translation of the solution found in
https://www.imo-official.org/problems/IMO2013SL.pdf
-/

open_locale big_operators

lemma le_of_all_pow_lt_succ {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
  (h : ∀ n : ℕ, 0 < n → x^n - 1 < y^n) :
  x ≤ y :=
begin
  by_contra hxy,
  push_neg at hxy,
  have hxmy : 0 < x - y := sub_pos.mpr hxy,
  have hn : ∀ n : ℕ, 0 < n → (x - y) * (n : ℝ) ≤ x^n - y^n,
  { intros n hn,
    have hterm : ∀ i : ℕ, i ∈ finset.range n → 1 ≤ x^i * y^(n - 1 - i),
    { intros i hi,
      have hx' : 1 ≤ x ^ i := one_le_pow_of_one_le hx.le i,
      have hy' : 1 ≤ y ^ (n - 1 - i) := one_le_pow_of_one_le hy.le (n - 1 - i),
      calc 1 ≤ x^i             : hx'
         ... = x^i * 1         : (mul_one _).symm
         ... ≤ x^i * y^(n-1-i) : mul_le_mul_of_nonneg_left hy' (zero_le_one.trans hx') },

    calc (x - y) * (n : ℝ)
            = (n : ℝ) * (x - y) : mul_comm _ _
        ... = (∑ (i : ℕ) in finset.range n, (1 : ℝ)) * (x - y) :
                                  by simp only [mul_one, finset.sum_const, nsmul_eq_mul,
                                    finset.card_range]
        ... ≤ (∑ (i : ℕ) in finset.range n, x ^ i * y ^ (n - 1 - i)) * (x-y) :
                                  (mul_le_mul_right hxmy).mpr (finset.sum_le_sum hterm)
        ... = x^n - y^n         : geom_sum₂_mul x y n, },

  -- Choose n larger than 1 / (x - y).
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - y)),
  have hNp : 0 < N, { exact_mod_cast (one_div_pos.mpr hxmy).trans hN },

  have := calc 1 = (x - y) * (1 / (x - y)) : by field_simp [ne_of_gt hxmy]
             ... < (x - y) * N             : (mul_lt_mul_left hxmy).mpr hN
             ... ≤ x^N - y^N               : hn N hNp,
  linarith [h N hNp]
end

/--
 Like le_of_all_pow_lt_succ, but with a weaker assumption for y.
-/
lemma le_of_all_pow_lt_succ' {x y : ℝ} (hx : 1 < x) (hy : 0 < y)
  (h : ∀ n : ℕ, 0 < n → x^n - 1 < y^n) :
  x ≤ y :=
begin
  refine le_of_all_pow_lt_succ hx _ h,
  by_contra hy'',
  push_neg at hy'', -- hy'' : y ≤ 1.

  -- Then there exists y' such that 0 < y ≤ 1 < y' < x.
  let y' := (x + 1) / 2,
  have h_y'_lt_x : y' < x,
  { have hh : (x + 1)/2 < (x * 2) / 2, { linarith },
    calc y' < (x * 2) / 2 : hh
        ... = x           : by field_simp },
  have h1_lt_y' : 1 < y',
  { have hh' : 1 * 2 / 2 < (x + 1) / 2, { linarith },
    calc 1 = 1 * 2 / 2 : by field_simp
       ... < y'        : hh' },
  have h_y_lt_y' : y < y' := hy''.trans_lt h1_lt_y',
  have hh : ∀ n, 0 < n → x^n - 1 < y'^n,
  { intros n hn,
    calc x^n - 1 < y^n  : h n hn
            ...  ≤ y'^n : pow_le_pow_of_le_left hy.le h_y_lt_y'.le n },
  exact h_y'_lt_x.not_le (le_of_all_pow_lt_succ hx h1_lt_y' hh)
end

lemma f_pos_of_pos {f : ℚ → ℝ} {q : ℚ} (hq : 0 < q)
  (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
  0 < f q :=
begin
  have num_pos : 0 < q.num := rat.num_pos_iff_pos.mpr hq,
  have hmul_pos :=
    calc (0 : ℝ) < q.num   : int.cast_pos.mpr num_pos
      ... = ((q.num.nat_abs : ℤ) : ℝ) : congr_arg coe (int.nat_abs_of_nonneg num_pos.le).symm
      ... ≤ f q.num.nat_abs           : H4 q.num.nat_abs
                                          (int.nat_abs_pos_of_ne_zero num_pos.ne')
      ... = f q.num : by { rw ←int.nat_abs_of_nonneg num_pos.le, norm_cast }
      ... = f (q * q.denom) : by rw ←rat.mul_denom_eq_num
      ... ≤ f q * f q.denom : H1 q q.denom hq (nat.cast_pos.mpr q.pos),
  have h_f_denom_pos :=
    calc (0 : ℝ) < q.denom : nat.cast_pos.mpr q.pos
      ... ≤ f q.denom : H4 q.denom q.pos,
  exact pos_of_mul_pos_right hmul_pos h_f_denom_pos.le,
end

lemma fx_gt_xm1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 ≤ x)
  (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
  (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
  (x - 1 : ℝ) < f x :=
begin
  have hx0 :=
    calc (x - 1 : ℝ)
          < ⌊x⌋₊   : by exact_mod_cast nat.sub_one_lt_floor x
      ... ≤ f ⌊x⌋₊ : H4 _ (nat.floor_pos.2 hx),

  obtain h_eq | h_lt := (nat.floor_le $ zero_le_one.trans hx).eq_or_lt,
  { rwa h_eq at hx0 },

  calc (x - 1 : ℝ) < f ⌊x⌋₊ : hx0
    ... < f (x - ⌊x⌋₊) + f ⌊x⌋₊ : lt_add_of_pos_left _ (f_pos_of_pos (sub_pos.mpr h_lt) H1 H4)
    ... ≤ f (x - ⌊x⌋₊ + ⌊x⌋₊)   : H2 _ _ (sub_pos.mpr h_lt) (nat.cast_pos.2 (nat.floor_pos.2 hx))
    ... = f x                   : by rw sub_add_cancel
end

lemma pow_f_le_f_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n) {x : ℚ} (hx : 1 < x)
  (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
  f (x^n) ≤ (f x)^n :=
begin
  induction n with pn hpn,
  { exfalso, exact nat.lt_asymm hn hn },
  cases pn,
  { simp only [pow_one] },
  have hpn' := hpn pn.succ_pos,
  rw [pow_succ' x (pn + 1), pow_succ' (f x) (pn + 1)],
  have hxp : 0 < x := zero_lt_one.trans hx,
  calc f ((x ^ (pn+1)) * x)
          ≤ f (x ^ (pn+1)) * f x : H1 (x ^ (pn+1)) x (pow_pos hxp (pn+1)) hxp
      ... ≤ (f x) ^ (pn+1) * f x : (mul_le_mul_right (f_pos_of_pos hxp H1 H4)).mpr hpn'
end

lemma fixed_point_of_pos_nat_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n)
  (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)
  (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x)
  {a : ℚ} (ha1 : 1 < a) (hae : f a = a) :
  f (a^n) = a^n :=
begin
  have hh0 : (a : ℝ) ^ n ≤ f (a ^ n),
  { exact_mod_cast H5 (a ^ n) (one_lt_pow ha1 hn.ne') },

  have hh1 := calc f (a^n) ≤ (f a)^n   : pow_f_le_f_pow hn ha1 H1 H4
                       ... = (a : ℝ)^n : by rw ← hae,

  exact hh1.antisymm hh0
end

lemma fixed_point_of_gt_1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 < x)
  (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
  (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)
  (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x)
  {a : ℚ} (ha1 : 1 < a) (hae : f a = a) :
  f x = x :=
begin
  -- Choose n such that 1 + x < a^n.
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 + x) ha1,
  have h_big_enough : (1:ℚ) < a^N - x := lt_sub_iff_add_lt.mpr hN,

  have h1 := calc (x : ℝ) + ((a^N - x) : ℚ)
                        ≤ f x + ((a^N - x) : ℚ) : add_le_add_right (H5 x hx) _
                    ... ≤ f x + f (a^N - x)     : add_le_add_left (H5 _ h_big_enough) _,

  have hxp : 0 < x := zero_lt_one.trans hx,

  have hNp : 0 < N,
  { by_contra H, push_neg at H, rw [nat.le_zero_iff.mp H] at hN, linarith },

  have h2 := calc f x + f (a^N - x)
                        ≤ f (x + (a^N - x)) : H2 x (a^N - x) hxp (zero_lt_one.trans h_big_enough)
                    ... = f (a^N)           : by ring_nf
                    ... = a^N               : fixed_point_of_pos_nat_pow hNp H1 H4 H5 ha1 hae
                    ... = x + (a^N - x)     : by ring,

  have heq := h1.antisymm (by exact_mod_cast h2),
  linarith [H5 x hx, H5 _ h_big_enough]
end

theorem imo2013_q5
  (f : ℚ → ℝ)
  (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
  (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
  (H_fixed_point : ∃ a, 1 < a ∧ f a = a) :
  ∀ x, 0 < x → f x = x :=
begin
  obtain ⟨a, ha1, hae⟩ := H_fixed_point,
  have H3 : ∀ x : ℚ, 0 < x → ∀ n : ℕ, 0 < n → ↑n * f x ≤ f (n * x),
  { intros x hx n hn,
    cases n,
    { exact (lt_irrefl 0 hn).elim },
    induction n with pn hpn,
    { simp only [one_mul, nat.cast_one] },
    calc (↑pn + 1 + 1) * f x
          = ((pn : ℝ) + 1) * f x + 1 * f x : add_mul (↑pn + 1) 1 (f x)
      ... = (↑pn + 1) * f x + f x          : by rw one_mul
      ... ≤ f ((↑pn.succ) * x) + f x       : by exact_mod_cast add_le_add_right
                                                  (hpn pn.succ_pos) (f x)
      ... ≤ f ((↑pn + 1) * x + x)          : by exact_mod_cast H2 _ _
                                                  (mul_pos pn.cast_add_one_pos hx) hx
      ... = f ((↑pn + 1) * x + 1 * x)      : by rw one_mul
      ... = f ((↑pn + 1 + 1) * x)          : congr_arg f (add_mul (↑pn + 1) 1 x).symm },
  have H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n,
  { intros n hn,
    have hf1 : 1 ≤ f 1,
    { have a_pos : (0 : ℝ) < a := rat.cast_pos.mpr (zero_lt_one.trans ha1),
      suffices : ↑a * 1 ≤ ↑a * f 1, from (mul_le_mul_left a_pos).mp this,
      calc ↑a * 1 = ↑a        : mul_one ↑a
              ... = f a       : hae.symm
              ... = f (a * 1) : by rw mul_one
              ... ≤ f a * f 1 : (H1 a 1) (zero_lt_one.trans ha1) zero_lt_one
              ... = ↑a * f 1  : by rw hae },

    calc (n : ℝ) = (n : ℝ) * 1   : (mul_one _).symm
             ... ≤ (n : ℝ) * f 1 : mul_le_mul_of_nonneg_left hf1 (nat.cast_nonneg _)
             ... ≤ f (n * 1)     : H3 1 zero_lt_one n hn
             ... = f n           : by rw mul_one },

  have H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x,
  { intros x hx,
    have hxnm1 : ∀ n : ℕ, 0 < n → (x : ℝ)^n - 1 < (f x)^n,
    { intros n hn,
      calc (x : ℝ)^n - 1 < f (x^n) : by exact_mod_cast fx_gt_xm1 (one_le_pow_of_one_le hx.le n)
                                          H1 H2 H4
                     ... ≤ (f x)^n : pow_f_le_f_pow hn hx H1 H4 },
    have hx' : 1 < (x : ℝ) := by exact_mod_cast hx,
    have hxp : 0 < x := zero_lt_one.trans hx,
    exact le_of_all_pow_lt_succ' hx' (f_pos_of_pos hxp H1 H4) hxnm1 },

  have h_f_commutes_with_pos_nat_mul : ∀ n : ℕ, 0 < n → ∀ x : ℚ, 0 < x → f (n * x) = n * f x,
  { intros n hn x hx,
    have h2 : f (n * x) ≤ n * f x,
    { cases n,
      { exfalso, exact nat.lt_asymm hn hn },
      cases n,
      { simp only [one_mul, nat.cast_one] },
      have hfneq : f (n.succ.succ) = n.succ.succ,
      { have := fixed_point_of_gt_1
                  (nat.one_lt_cast.mpr (nat.succ_lt_succ n.succ_pos)) H1 H2 H4 H5 ha1 hae,
        rwa (rat.cast_coe_nat n.succ.succ) at this },
      rw ← hfneq,
      exact H1 (n.succ.succ : ℚ) x (nat.cast_pos.mpr hn) hx },
    exact h2.antisymm (H3 x hx n hn) },

  -- For the final calculation, we expand x as (2*x.num) / (2*x.denom), because
  -- we need the top of the fraction to be strictly greater than 1 in order
  -- to apply fixed_point_of_gt_1.
  intros x hx,
  let x2denom := 2 * x.denom,
  let x2num := 2 * x.num,

  have hx2pos := calc 0 < x.denom           : x.pos
                    ... < x.denom + x.denom : lt_add_of_pos_left x.denom x.pos
                    ... = 2 * x.denom       : by ring,

  have hxcnez   : (x.denom : ℚ) ≠ (0 : ℚ) := ne_of_gt (nat.cast_pos.mpr x.pos),
  have hx2cnezr : (x2denom : ℝ) ≠ (0 : ℝ) := nat.cast_ne_zero.mpr (ne_of_gt hx2pos),

  have hrat_expand2 := calc x = x.num / x.denom : by exact_mod_cast rat.num_denom.symm
                          ... = x2num / x2denom : by { field_simp [-rat.num_div_denom], linarith },

  have h_denom_times_fx :=
    calc (x2denom : ℝ) * f x = f (x2denom * x)                 : (h_f_commutes_with_pos_nat_mul
                                                                    x2denom hx2pos x hx).symm
                         ... = f (x2denom * (x2num / x2denom)) : by rw hrat_expand2
                         ... = f x2num                         : by { congr, field_simp, ring },

  have h_fx2num_fixed : f x2num = x2num,
  { have hx2num_gt_one : (1 : ℚ) < (2 * x.num : ℤ),
    { norm_cast, linarith [rat.num_pos_iff_pos.mpr hx] },
    have hh := fixed_point_of_gt_1 hx2num_gt_one H1 H2 H4 H5 ha1 hae,
    rwa (rat.cast_coe_int x2num) at hh },

  calc f x = f x * 1                                 : (mul_one (f x)).symm
       ... = f x * (x2denom / x2denom)               : by rw ←(div_self hx2cnezr)
       ... = (f x * x2denom) / x2denom               : mul_div_assoc' (f x) _ _
       ... = (x2denom * f x) / x2denom               : by rw mul_comm
       ... = f x2num / x2denom                       : by rw h_denom_times_fx
       ... = x2num / x2denom                         : by rw h_fx2num_fixed
       ... = (((x2num : ℚ) / (x2denom : ℚ) : ℚ) : ℝ) : by norm_cast
       ... = x                                       : by rw ←hrat_expand2
end

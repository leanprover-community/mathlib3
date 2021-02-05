/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import analysis.transcendental.liouville
import data.nat.factorial

/-!
# Liouville constants

This files contains a construction of a family of Liouville number.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `is_liouville.is_transcendental_of_liouville_constant`.
-/

namespace is_liouville

noncomputable theory
open_locale nat big_operators classical
open set real finset

section m_is_real

variable {m : ℝ}

section lemmas_about_summability_and_sums

@[simp] lemma tsum_ite_eq' (i : ℕ) (a : ℝ) :
  ∑' n, (ite (n = i) a 0) = a :=
begin
  convert tsum_ite_eq i a,
  funext, congr,
end

lemma tsum_ite_eq_add {f : ℕ → ℝ} (hf : summable f) (i : ℕ) (a : ℝ) :
  ∑' n, ((ite (n = i) a 0) + f n) = a + ∑' n, f n :=
begin
  rw [tsum_add ⟨a, _⟩ hf, @tsum_eq_single ℝ _ _ _ _ _ i],
  { split_ifs; refl },
  { exact λ (j : ℕ) (ji : ¬ j = i), @if_neg _ _ ji _ _ _ },
  { convert has_sum_ite_eq i a,
    refine funext (λ x, _),
    congr }
end

lemma tsum_congr {f g : ℕ → ℝ} (hfg : ∀ n, f n = g n) :
  ∑' n, f n = ∑' n, g n :=
congr_arg tsum (funext hfg)

lemma tsum_ite_eq_extract {f : ℕ → ℝ} (hf : summable f) (i : ℕ) :
  ∑' n, f n = f i + ∑' n, ite (n ≠ i) (f n) 0 :=
by rw [← tsum_ite_eq_add (hf.summable_of_eq_zero_or_self (λ j, _)) i, tsum_congr (λ j, _)];
  by_cases ji : j = i; simp [ji]

lemma tsum_lt {f g : ℕ → ℝ} (h : ∀ (b : ℕ), f b ≤ g b)
  (hf: summable f) (hg: summable g) {i : ℕ} (hi : f i < g i) :
  ∑' n, f n < ∑' n, g n :=
begin
  rw [tsum_ite_eq_extract hf i, tsum_ite_eq_extract hg i],
  refine add_lt_add_of_lt_of_le hi (tsum_le_tsum (λ j, _) _ _),
  by_cases ji : j = i; simp [ji]; exact h j,
  { refine hf.summable_of_eq_zero_or_self (λ j, _),
    by_cases ji : j = i; simp [ji] },
  { refine hg.summable_of_eq_zero_or_self (λ j, _),
    by_cases ji : j = i; simp [ji] }
end

lemma tsum_lt_of_nonneg {f g : ℕ → ℝ} (h0 : ∀ (b : ℕ), 0 ≤ f b) (h : ∀ (b : ℕ), f b ≤ g b)
  (hg: summable g) {i : ℕ} (hi : f i < g i) :
  ∑' n, f n < ∑' n, g n :=
tsum_lt h (summable_of_nonneg_of_le h0 h hg) hg hi

variable (hm : 1 < m)

include hm

/-- An easy criterion for convergence of a series. -/
lemma summable_inv_pow_ge {ex : ℕ → ℕ} (exi : ∀ i, i ≤ ex i) :
  summable (λ i, 1 / (m : ℝ) ^ ex i) :=
begin
  refine summable_of_nonneg_of_le
    (λ a, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (λ a, _)
    (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
      ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (by rwa one_div_one))),
  rw [div_pow, one_pow],
  refine (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (exi a)),
  repeat { exact pow_pos (zero_lt_one.trans hm) _ },
end

/-- This series is explicitly proven, since it is used twice in the remaining lemmas. -/
lemma summable_inv_pow_n_add_fact (n : ℕ) :
  summable (λ i, 1 / (m : ℝ) ^ (i + (n + 1))!) :=
summable_inv_pow_ge hm (λ i, (nat.self_le_factorial _).trans (nat.factorial_le (nat.le.intro rfl)))

omit hm

section natural
open nat
lemma lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n! :=
begin
  rw [← succ_pred_eq_of_pos (lt_of_lt_of_le (zero_lt_two.trans (lt.base 2)) hi), factorial_succ],
  refine lt_mul_of_one_lt_right ((pred n).succ_pos) (lt_of_lt_of_le _ (self_le_factorial _)),
  exact lt_of_lt_of_le one_lt_two (le_pred_of_lt (succ_le_iff.mp hi)),
end

lemma factorial_one_lt_iff {n : ℕ} : n < factorial n ↔ n ≠ 1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  by_contra k,
  rw not_not at k,
  rw k at h,
  exact not_le.mpr h (le_of_eq factorial_one),
  apply lt_iff_le_and_ne.mpr ⟨self_le_factorial _, λ k, h _⟩,
  by_cases n0 : n = 0,
  { rw [n0, factorial_zero, factorial_one] at k,
    exact (rfl.congr k).mp n0 },
  have : n = n.pred.succ := (succ_pred_eq_of_pos (zero_lt_iff.mpr n0)).symm,
  rw [this] at k { occs := occurrences.pos [2] },
  rw [factorial_succ, succ_eq_add_one, add_mul] at k,
  nth_rewrite 1 [this] at k,

  rw [not_le, lt_succ_iff] at k,
  cases k with k k,
  exact not_le.mpr h (le_of_eq factorial_one),
  change n ≤ 0 at k,
  rw nat.le_zero_iff at k,
  apply lt_of_lt_of_le _ (le_of_eq factorial_one.symm),
  rw factorial_one at h,
  exact nat.lt_asymm h h,

  rw [not_le, lt_succ_iff, ← factorial_eq_one] at k,
  rw k at h,
  rw factorial_eq_one at k,
  symmetry,
  by_contra,
  rw [not_iff,not_le, lt_succ_iff] at h,
  rw ← factorial_eq_one at h,
  have : n < 2 ↔ n ≤ 1,exact lt_succ_iff,
end

lemma add_factorial_lt_factorial_add_fewer_rw {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
  i + n.succ! < (i + n.succ)! :=
begin
  rw [succ_eq_add_one, ← add_assoc, factorial_succ (i + _), succ_eq_add_one, add_mul, one_mul],
  have : i ≤ i + n := le.intro rfl,
  exact add_lt_add_of_lt_of_le (lt_of_le_of_lt this ((lt_mul_iff_one_lt_right (lt_of_lt_of_le
    zero_lt_two (hi.trans this))).mpr (lt_iff_le_and_ne.mpr ⟨(i + n).factorial_pos, λ g,
    nat.not_succ_le_self 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩))) (factorial_le
    ((le_of_eq (add_comm n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi)))),
end

lemma add_factorial_lt_factorial_add_cases {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
  i + n.succ! < (i + n.succ)! :=
begin
  by_cases n0 : n = 0,
  { rw [n0],
    exact lt_of_lt_of_le (lt_factorial_self (succ_le_succ hi)) (le_of_eq rfl) },
  rw [succ_eq_add_one, ← add_assoc, factorial_succ (i + _), succ_eq_add_one, add_mul, one_mul],
  have : i < i + n := (lt_add_iff_pos_right _).mpr (zero_lt_iff.mpr n0),
  refine add_lt_add_of_lt_of_le (lt_of_lt_of_le this _) _,
  refine (le_mul_iff_one_le_right (lt_trans (lt_of_lt_of_le zero_lt_two hi) this)).mpr (factorial_pos _),
  exact factorial_le ((le_of_eq (add_comm n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi))),
end


lemma add_factorial_lt_factorial_add {i : ℕ} (n : ℕ) (hi : 2 ≤ i) : i + n.succ! < (i + n.succ)! :=
begin
  by_cases n0 : n = 0,
  { rw [n0],
    exact lt_of_lt_of_le (lt_factorial_self (succ_le_succ hi)) (le_of_eq rfl) },
  rw [factorial_succ, succ_eq_add_one, add_mul, one_mul, ← add_assoc, ← add_assoc, factorial_succ],
  simp only [succ_eq_add_one, add_mul, one_mul],
  repeat { refine add_lt_add _  _ },
  apply (lt_mul_iff_one_lt_right _).mpr,
  refine lt_of_le_of_lt (le_of_eq factorial_one.symm) ((factorial_lt zero_lt_one).mpr _),
  apply lt_add_right,
  any_goals { refine lt_of_lt_of_le _ hi, exact zero_lt_two <|> exact one_lt_two },
  apply mul_lt_mul_of_pos_left _ (zero_lt_iff.mpr n0),
  any_goals { exact (factorial_lt (zero_lt_iff.mpr n0)).mpr
    ((lt_add_iff_pos_left _).mpr (lt_of_lt_of_le zero_lt_two hi)) },
end

lemma add_le_mul_two_add {R : Type*} [ordered_semiring R] [nontrivial R] {a b : R}
  (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
(((add_le_add_left (add_le_add a2 (le_mul_of_one_le_left b0 (one_le_two.trans a2))) a).trans
  (le_of_eq (add_assoc a a _).symm)).trans (add_le_add_right (le_of_eq (mul_two a).symm) _)).trans
  (le_of_eq (mul_add a 2 b).symm)

lemma add_le_mul {a b : ℕ} (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
begin
  rcases le_iff_exists_add.mp b2 with ⟨k, rfl⟩,
  exact add_le_mul_two_add a2 k.zero_le
end

lemma add_factorial_lt_factorial_add_ind {i : ℕ} (n : ℕ) (hi : 2 ≤ i) : i + n.succ! < (i + n.succ)! :=
begin
  induction n with n hn,
  { exact lt_of_lt_of_le (lt_factorial_self (succ_le_succ hi)) (le_of_eq rfl) },
  rw [add_succ, factorial_succ (i + _)],
  simp [succ_eq_add_one, add_mul, mul_add, ← add_assoc],
  repeat { refine add_lt_add _  _ },
  apply (lt_mul_iff_one_lt_right _).mpr,
  refine lt_of_le_of_lt (le_of_eq factorial_one.symm) ((factorial_lt zero_lt_one).mpr _),
  apply lt_add_right,
  any_goals { refine lt_of_lt_of_le _ hi, exact zero_lt_two <|> exact one_lt_two },
  apply mul_lt_mul_of_pos_left _ (zero_lt_iff.mpr n0),
  any_goals { exact (factorial_lt (zero_lt_iff.mpr n0)).mpr
    ((lt_add_iff_pos_left _).mpr (lt_of_lt_of_le zero_lt_two hi)) },
end
end natural

/-
lemma add_factorial_le_factorial_add (i n : ℕ) (n0 : n ≠ 0) (hi : 2 ≤ i) : i + n! < (i + n)! :=
begin
  induction i with i ih,
  { cases hi },
  { simp only [nat.succ_eq_add_one, add_right_comm _ 1, nat.factorial_succ],
    rw [add_mul (i + n), one_mul, add_comm _ 1],
    by_cases i0 : i = 0,
    { subst i0, exact (nat.not_succ_le_self 1 hi).elim },
    by_cases i0 : i = 1,
    { subst i0,
      simp,
    },

    apply add_le_add _ ih,
    exact mul_pos (nat.add_pos_right _ (nat.pos_of_ne_zero hn)) (nat.factorial_pos _) }
end


omit hm
-/

theorem pow_le_pow_of_le_r {a : ℝ} {n m : ℕ} (a0 : 0 ≤ a) (a1 : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
pow_le_pow_of_le_one a0 a1 h

lemma calc_liou_one_le_no_calc_ep {ε : ℝ} (e0 : 0 ≤ ε) (e1 : ε ≤ 1) (n i : ℕ) :
ε ^ (i + (n + 1))! ≤ ε ^ i * ε ^ (n + 1)! :=
(pow_le_pow_of_le_one e0 e1 (i.add_factorial_le_factorial_add n.succ n.succ_ne_zero)).trans
  (le_of_eq (pow_add ε i (n + 1)!))

lemma one_div_pow_le_one_div_pow {R : Type*} [linear_ordered_field R] {n m : ℕ} {a : R}
  (h : n ≤ m) (a1 : 1 ≤ a) :
  1 / a ^ m ≤ 1 / a ^ n :=
(one_div_le_one_div (pow_pos (lt_of_lt_of_le zero_lt_one a1) _)
  (pow_pos (lt_of_lt_of_le zero_lt_one a1) _)).mpr (pow_mono a1 h)

lemma calc_liou_one_le_no_calc (m1 : 1 ≤ m) (n : ℕ) (i : ℕ) :
1 / m ^ (i + (n + 1))! ≤ 1 / m ^ i * 1 / m ^ (n + 1)! :=
begin
  refine (le_of_eq (one_div_pow (i + (n + 1))!).symm).trans ((calc_liou_one_le_no_calc_ep
    (one_div_nonneg.mpr (zero_le_one.trans m1)) ((one_div_le (lt_of_lt_of_le (@zero_lt_one ℝ _ _)
      m1) zero_lt_one).mpr ((le_of_eq one_div_one).trans m1)) n i).trans
      (le_trans _ (le_of_eq (mul_div_assoc).symm))),
    rw ← one_div_pow,
    exact (mul_le_mul_left (pow_pos (one_div_pos.mpr
      (lt_of_lt_of_le (@zero_lt_one ℝ _ _) m1)) i)).mpr (le_of_eq (one_div_pow _))
end

lemma calc_liou_one_le (m1 : 1 ≤ m) (n : ℕ) (i : ℕ) :
1 / m ^ (i + (n + 1))! ≤ (1 / m) ^ i * 1 / m ^ (n + 1)! :=
begin
  rw [one_div_pow],
  exact calc_liou_one_le_no_calc m1 n i,
end

/--  Partial inequality, works with `m ∈ ℝ` and satisfying `1 < m`. -/
lemma calc_liou_one (m1 : 1 < m) (n : ℕ) :
∑' (i : ℕ), 1 / m ^ (i + (n + 1))! < m / (m - 1) * (1 / m ^ (n + 1)!) :=
begin
  have m0 : 0 < m := (lt_trans zero_lt_one m1),
  have mi : abs (1 / m) < 1,
  { rw abs_of_pos (one_div_pos.mpr m0),
    exact (div_lt_one m0).mpr m1 },

  have : (∑' (i : ℕ), (1 / m) ^ i) * (1 / m ^ (n + 1)!) = m / (m - 1) * (1 / m ^ (n + 1)!),
  { refine (mul_left_inj' (ne_of_gt (one_div_pos.mpr (pow_pos m0 _)))).mpr _,
    rw [tsum_geometric_of_abs_lt_1 mi, inv_eq_one_div],
    refine (div_eq_iff (ne_of_gt (sub_pos.mpr ((one_div_lt m0 zero_lt_one).mpr
      (lt_of_le_of_lt (le_of_eq (div_one 1)) m1))))).mpr _,
    rw [div_mul_eq_mul_div, mul_sub, mul_one, mul_one_div_cancel (ne_of_gt m0),
      div_self (ne_of_gt (sub_pos.mpr m1))] },
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) : tsum_lt_of_nonneg
      (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
      (λ b, (one_div_le_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr
        (pow_le_pow m1.le (nat.add_factorial_le_factorial_add _ _ (nat.succ_ne_zero _))))
      (summable_inv_pow_ge m1 (λ j, nat.le.intro rfl))
      ((one_div_lt_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr
        (pow_lt_pow m1 (add_factorial_lt_factorial_add n rfl.le)))
... = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    by { congr, ext i, rw [pow_add, div_pow, one_pow, ←div_div_eq_div_mul, div_eq_mul_one_div] }
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = m / (m - 1) * (1 / m ^ (n + 1)!) :
    begin
      rw [tsum_geometric_of_abs_lt_1 mi, show (m / (m - 1)) = ((m - 1) / m)⁻¹,
        by rw inv_div, sub_div, div_self (ne_of_gt m0)]
    end,
end

lemma le_pow_self {a : ℝ} {n : ℕ} (n0 : 0 < n) (a1 : 1 ≤ a) : a ≤ a ^ n :=
(le_of_eq (pow_one a).symm).trans (pow_mono a1 (nat.succ_le_iff.mpr n0))

lemma calc_liou_two_zero (n : ℕ) (hm : 2 ≤ m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
begin
  calc m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :
    mul_le_mul ((div_le_iff (sub_pos.mpr (lt_of_lt_of_le (@one_lt_two ℝ _ _) hm))).mpr
    (le_trans (le_sub.mpr ((le_of_eq (mul_one 2)).trans (has_le.le.trans hm (le_of_eq
    (eq_sub_iff_add_eq.mpr (two_mul m).symm))))) (le_of_eq (mul_sub 2 m 1).symm))) rfl.le
    (one_div_nonneg.mpr (le_of_lt (pow_pos (lt_of_lt_of_le zero_lt_two hm) (n + 1)!))) zero_le_two
  ... = 2 / m ^ (n + 1)! : mul_one_div 2 _
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... ≤ 1 / m ^ (n! * n) :
    begin
      rw [div_le_div_iff, one_mul],
      conv_rhs { rw [mul_add, pow_add, mul_one, pow_mul, mul_comm] },
      refine mul_le_mul (hm.trans (le_pow_self (nat.factorial_pos n) (one_le_two.trans hm)))
        (le_of_eq (pow_mul _ _ _)) (le_of_lt _) (le_of_lt _),
      any_goals { exact pow_pos (lt_of_lt_of_le zero_lt_two hm) _ },
    end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul
end

--strict inequality in the statement, but does not allow m = 2
lemma calc_liou_two (n : ℕ) (hm : 2 < m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) < 1 / (m ^ n!) ^ n :=
calc m / (m - 1) * (1 / m ^ (n + 1)!) < 2 * (1 / m ^ (n + 1)!) :
  begin
    refine mul_lt_mul _ le_rfl (one_div_pos.mpr (pow_pos (zero_lt_two.trans hm) _)) zero_le_two,
    rwa [div_lt_iff, mul_sub, mul_one, lt_sub_iff_add_lt, two_mul, real.add_lt_add_iff_left],
    exact lt_sub_iff_add_lt.mpr (by { rw zero_add, exact (one_lt_two.trans hm) })
  end
  ... = 2 / m ^ (n + 1)! : mul_one_div 2 _
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... < 1 / m ^ (n! * n) :
  begin
    rw [div_lt_div_iff, one_mul],
    conv_rhs { rw [mul_add, pow_add, mul_one, pow_mul, mul_comm] },
    apply mul_lt_mul,
    { refine lt_of_lt_of_le hm _,
      conv_lhs { rw ← pow_one m },
      exact pow_le_pow (one_le_two.trans hm.le) (nat.factorial_pos _) },
    { rw pow_mul },
    any_goals { try {refine le_of_lt _}, exact pow_pos (zero_lt_two.trans hm) _ }
  end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul

lemma calc_liou_one_lt (m1 : 1 < m) (n : ℕ) (i : ℕ) (hi : 2 ≤ i) :
1 / m ^ (i + (n + 1))! < 1 / m ^ i * 1 / m ^ (n + 1)! :=
begin
  rw [mul_div_assoc, one_div_mul_one_div, ← pow_add],
  refine (one_div_lt_one_div _ _).mpr (pow_lt_pow m1 (n.add_factorial_lt_factorial_add hi)),
  repeat { exact pow_pos (zero_lt_one.trans m1) _ },
end

end lemmas_about_summability_and_sums

/--
liouville constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant (m : ℝ) := ∑' (i : ℕ), 1 / m ^ i!
/--
`liouville_constant_first_k_terms` is the first `k` terms of the liouville constant, i.e
$$
\sum_{i=0}^k\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant_first_k_terms (m : ℝ) (k : ℕ) := ∑ i in range (k+1), 1 / m ^ i!
/--
`liouville_constant_terms_after_k` is all the terms start from `k+1` of the liouville constant, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant_terms_after_k (m : ℝ) (k : ℕ) :=  ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_constant_terms_after_pos (hm : 1 < m) :
  ∀ k, 0 < liouville_constant_terms_after_k m k := λ n,
calc 0 < 1 / (m : ℝ) ^ (n + 1)! : one_div_pos.mpr (pow_pos (lt_trans zero_lt_one hm) _)
  ... = 1 / (m : ℝ) ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / (m : ℝ) ^ (i + (n + 1))! :
      le_tsum (summable_inv_pow_n_add_fact hm _) 0
        (λ i i0, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))

lemma liouville_constant_eq_first_k_terms_add_rest (hm : 1 < m) (k : ℕ):
  liouville_constant m = liouville_constant_first_k_terms m k +
  liouville_constant_terms_after_k m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, nat.self_le_factorial i))).symm

end m_is_real


section m_is_natural

variable {m : ℕ}

lemma rat_of_liouville_constant_first_k_terms (hm : 1 < m) (k : ℕ) :
∃ p : ℕ, liouville_constant_first_k_terms m k = p / (m ^ k!) :=
begin
  induction k with k h,
  { exact ⟨1, by rw [liouville_constant_first_k_terms, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    unfold liouville_constant_first_k_terms at h_k ⊢,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring },
    refine mul_ne_zero_iff.mpr ⟨_, _⟩,
    all_goals { refine pow_ne_zero _ _, exact_mod_cast ne_of_gt (lt_trans zero_lt_one hm), } }
end

theorem is_liouville_liouville_constant (hm : 2 ≤ m) :
  is_liouville (liouville_constant m) :=
begin
  have mZ1 : 1 < (m : ℤ) := lt_of_le_of_lt (le_of_eq nat.cast_one.symm)
    (lt_of_lt_of_le one_lt_two ((le_of_eq nat.cast_two.symm).trans (int.to_nat_le.mp hm))),
  have m1 : 1 < (m : ℝ) :=
    lt_of_lt_of_le one_lt_two ((le_of_eq nat.cast_two.symm).trans (nat.cast_le.mpr hm)),
  intro n,
  have h_truncation_wd := liouville_constant_eq_first_k_terms_add_rest m1 n,
  rcases rat_of_liouville_constant_first_k_terms (lt_of_lt_of_le one_lt_two hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 (nat.factorial_pos n), _⟩,
  push_cast,
  rw [← hp, h_truncation_wd, add_sub_cancel', abs_of_pos (liouville_constant_terms_after_pos m1 _)],
  exact ⟨ne_of_gt ((lt_add_iff_pos_right _).mpr (liouville_constant_terms_after_pos m1 n)),
    lt_of_lt_of_le (calc_liou_one m1 n) (calc_liou_two_zero _ ((le_of_eq nat.cast_two.symm).trans
      (nat.cast_le.mpr hm)))⟩
end

lemma is_transcendental_liouville_constant (hm : 2 ≤ m) :
  is_transcendental ℤ (liouville_constant m) :=
transcendental_of_is_liouville (is_liouville_liouville_constant hm)

end m_is_natural

end is_liouville

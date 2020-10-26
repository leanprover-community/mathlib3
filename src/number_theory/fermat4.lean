/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Paul van Wamelen.
-/
import number_theory.pythagorean_triples
import ring_theory.coprime

/-!
# Fermat's Last Theorem for the case n = 4
There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/

noncomputable theory
open_locale classical

/-- Shorthand for three non-zero integers `a`, `b`, and `c` satisfying `a ^ 4 + b ^ 4 = c ^ 2`.
We will show that no integers satisfy this equation. Clearly Fermat's Last theorem for n = 4
follows. -/
def fermat_42 (a b c : ℤ) : Prop := a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

namespace fermat_42

lemma comm {a b c : ℤ} :
 (fermat_42 a b c) ↔ (fermat_42 b a c) :=
 by { delta fermat_42, rw add_comm, tauto }

lemma mul {a b c k : ℤ} (hk0 : k ≠ 0) :
  fermat_42 a b c ↔ fermat_42 (k * a) (k * b) (k ^ 2 * c) :=
begin
  delta fermat_42,
  split,
  { intro f42,
    split, { exact mul_ne_zero hk0 f42.1 },
    split, { exact mul_ne_zero hk0 f42.2.1 },
    { calc (k * a) ^ 4 + (k * b) ^ 4
          = k ^ 4 * (a ^ 4 + b ^ 4) : by ring
      ... = k ^ 4 * c ^ 2 : by rw f42.2.2
      ... = (k ^ 2 * c) ^ 2 : by ring }},
  { intro f42,
    split, { exact right_ne_zero_of_mul f42.1 },
    split, { exact right_ne_zero_of_mul f42.2.1 },
    apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp,
    { calc k ^ 4 * (a ^ 4 + b ^ 4)
          = (k * a) ^ 4 + (k * b) ^ 4 : by ring
      ... = (k ^ 2 * c) ^ 2 : by rw f42.2.2
      ... = k ^ 4 * c ^ 2 : by ring }}
end

lemma ne_zero {a b c : ℤ} (h : fermat_42 a b c) : c ≠ 0 :=
begin
  apply ne_zero_pow (dec_trivial : 2 ≠ 0), apply ne_of_gt,
  rw [← h.2.2, (by ring : a ^ 4 + b ^ 4 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2)],
  exact add_pos (pow_two_pos_of_ne_zero _ (pow_ne_zero 2 h.1))
      (pow_two_pos_of_ne_zero _ (pow_ne_zero 2 h.2.1))
end

/-- We say a solution to `a ^ 4 + b ^ 4 = c ^ 2` is minimal if there is no other solution with
a smaller `c` (in absolute value). -/
def minimal (a b c : ℤ) : Prop :=
  (fermat_42 a b c) ∧ ∀ (a1 b1 c1 : ℤ), (fermat_42 a1 b1 c1) → int.nat_abs c ≤ int.nat_abs c1

/-- if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/
lemma exists_minimal {a b c : ℤ} (h : fermat_42 a b c) :
  ∃ (a0 b0 c0), (minimal a0 b0 c0) :=
begin
  let all : set (ℤ × ℤ × ℤ) := {s | fermat_42 s.1 s.2.1 s.2.2},
  let S : set (ℕ) := { n | ∃ (s : ℤ × ℤ × ℤ), fermat_42 s.1 s.2.1 s.2.2 ∧ n = int.nat_abs s.2.2},
  have S_nonempty : S.nonempty,
  { use int.nat_abs c,
    rw set.mem_set_of_eq,
    use ⟨a, ⟨b, c⟩⟩, tauto },
  let m : ℕ := well_founded.min nat.lt_wf S S_nonempty,
  have m_mem : m ∈ S            := well_founded.min_mem nat.lt_wf S S_nonempty,
  have m_min : ∀ k ∈ S, ¬ k < m := λ k hk, well_founded.not_lt_min nat.lt_wf S S_nonempty hk,
  rw set.mem_set_of_eq at m_mem,
  cases m_mem with s0 hs0,
  use [s0.1, s0.2.1, s0.2.2],
  split,
  { exact hs0.1 },
  { intros a1 b1 c1 h1,
    refine not_lt.mp _,
    rw ← hs0.2,
    apply m_min,
    rw set.mem_set_of_eq,
    use ⟨a1, ⟨b1, c1⟩⟩, tauto }
end

/-- a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` must have `a` and `b` coprime. -/
lemma coprime_of_minimal {a b c : ℤ} (h : minimal a b c) :
  int.gcd a b = 1 :=
begin
  by_contradiction hab,
  obtain ⟨p, hp, hpa, hpb⟩ := nat.prime.not_coprime_iff_dvd.mp hab,
  obtain ⟨a1, ha1⟩ := exists_eq_mul_right_of_dvd (int.coe_nat_dvd_left.mpr hpa),
  obtain ⟨b1, hb1⟩ := exists_eq_mul_right_of_dvd (int.coe_nat_dvd_left.mpr hpb),
  have hpc : (p : ℤ) ^ 2 ∣ c,
  { apply (int.pow_dvd_pow_iff (dec_trivial : 0 < 2)).mp,
    rw [← h.1.2.2, ha1, hb1],
    apply dvd.intro (a1 ^ 4 + b1 ^ 4), ring },
  obtain ⟨c1, hc1⟩ := exists_eq_mul_right_of_dvd hpc,
  have hf : fermat_42 a1 b1 c1,
  { apply (fermat_42.mul (int.coe_nat_ne_zero.mpr (nat.prime.ne_zero hp))).mpr,
    rw [← ha1, ← hb1, ← hc1], exact h.1 },
  apply nat.le_lt_antisymm (h.2 _ _ _ hf),
  rw [hc1, int.nat_abs_mul],
  rw [← one_mul (int.nat_abs c1)] {occs := occurrences.pos [1]},
  rw mul_lt_mul_right (nat.pos_of_ne_zero (int.nat_abs_ne_zero_of_ne_zero (ne_zero hf))),
  rw [pow_two, int.nat_abs_mul, int.nat_abs_of_nat],
  refine nat.sqrt_lt.mp _, rw [← one_mul 1, nat.sqrt_eq], exact nat.prime.one_lt hp
end

/-- We can swap `a` and `b` in a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2`. -/
lemma minimal_comm {a b c : ℤ} :
 (minimal a b c) → (minimal b a c) :=
begin
  rintros ⟨h1, h2⟩,
  split, { exact fermat_42.comm.mp h1 },
  exact h2
end

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has positive `c`. -/
lemma neg_of_minimal {a b c : ℤ} :
 (minimal a b c) → (minimal a b (-c)) :=
begin
  rintros ⟨⟨ha, hb, heq⟩, h2⟩,
  split,
  { apply and.intro ha (and.intro hb _),
    rw heq, exact (neg_square c).symm },
  rw (int.nat_abs_neg c), exact h2
end

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has `a` odd. -/
lemma exists_odd_minimal {a b c : ℤ} (h : fermat_42 a b c) :
  ∃ (a0 b0 c0), (minimal a0 b0 c0) ∧ a0 % 2 = 1 :=
begin
  obtain ⟨a0, b0, c0, hf⟩ := exists_minimal h,
  cases int.mod_two_eq_zero_or_one a0 with hap hap,
  { cases int.mod_two_eq_zero_or_one b0 with hbp hbp,
    { exfalso,
      have h1 : 2 ∣ (int.gcd a0 b0 : ℤ),
      { exact int.dvd_gcd (int.dvd_of_mod_eq_zero hap) (int.dvd_of_mod_eq_zero hbp) },
        rw (coprime_of_minimal hf) at h1, revert h1, norm_num },
      { exact ⟨b0, ⟨a0, ⟨c0, minimal_comm hf, hbp⟩⟩⟩ }},
  exact ⟨a0, ⟨b0, ⟨c0 , hf, hap⟩⟩⟩,
end

/-- We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has
`a` odd and `c` positive. -/
lemma exists_pos_odd_minimal {a b c : ℤ} (h : fermat_42 a b c) :
  ∃ (a0 b0 c0), (minimal a0 b0 c0) ∧ a0 % 2 = 1 ∧ 0 < c0  :=
begin
  obtain ⟨a0, b0, c0, hf, hc⟩ := exists_odd_minimal h,
  by_cases h0 : 0 < c0,
  { use [a0, b0, c0], tauto },
  { use [a0, b0, -c0],
    apply and.intro (neg_of_minimal hf),
    apply and.intro hc,
    apply neg_pos.mpr, apply not_le.mp, intro h2,
    have h3 : 0 < c0, { exact lt_of_le_of_ne h2 (ne.symm (ne_zero hf.1)) },
    revert h3, exact h0 }
end

end fermat_42

lemma int.coprime_of_sqr_sum_delete {m r s : ℤ} (h : m = r ^ 2 + s ^ 2) (h2 : int.gcd r s = 1) :
  int.gcd m r = 1 :=
begin
  by_contradiction hg,
  obtain ⟨p, ⟨hp, hm, hr⟩⟩ := nat.prime.not_coprime_iff_dvd.mp hg,
  apply nat.prime.not_dvd_one hp,
  rw ← h2,
  apply nat.dvd_gcd hr,
  apply int.coe_nat_dvd_left.mp,
  apply (or_self _).mp (int.prime.dvd_mul' hp _),
  rw [← pow_two, (eq_sub_of_add_eq' (eq.symm h))],
  apply dvd_sub (int.coe_nat_dvd_left.mpr hm),
  rw pow_two, exact dvd_mul_of_dvd_left (int.coe_nat_dvd_left.mpr hr) r
end

lemma int.coprime_of_sqr_sum {m r s : ℤ} (h : m = r ^ 2 + s ^ 2) (h2 : int.gcd r s = 1) :
  int.gcd m r = 1 :=
begin
  apply int.gcd_eq_one_iff_coprime.mpr,
  rw [h, pow_two, pow_two],
  apply is_coprime.mul_add_left_left _ r,
  apply is_coprime.mul_left;
  { apply int.gcd_eq_one_iff_coprime.mp, rw int.gcd_comm, exact h2 },
end

lemma int.coprime_of_sqr_sum_delete' {m r s : ℤ} (h : m = r ^ 2 + s ^ 2) (h2 : int.gcd r s = 1) :
  int.gcd m (r * s) = 1 :=
begin
  dunfold int.gcd,
  rw int.nat_abs_mul,
  apply nat.coprime.mul_right (int.coprime_of_sqr_sum h h2),
  rw add_comm at h,
  rw [int.gcd_comm r s] at h2,
  exact int.coprime_of_sqr_sum h h2
end

lemma int.coprime_of_sqr_sum' {m r s : ℤ} (h : m = r ^ 2 + s ^ 2) (h2 : int.gcd r s = 1) :
  int.gcd m (r * s) = 1 :=
begin
  apply int.gcd_eq_one_iff_coprime.mpr,
  rw [h, pow_two, pow_two],
end

namespace fermat_42

-- If we have a solution to a ^ 4 + b ^ 4 = c ^ 2, we can construct a smaller one. This
-- implies there can't be a smallest solution.
lemma not_minimal {a b c : ℤ}
  (h : minimal a b c) (ha2 : a % 2 = 1) (hc : 0 < c) : false :=
begin
  -- Use the fact that a ^ 2, b ^ 2, c form a pythagorean triple to obtain m and n such that
  -- a ^ 2 = m ^ 2 - n ^ 2, b ^ 2 = 2 * m * n and c = m ^ 2 + n ^ 2
  -- first the formula:
  have ht : pythagorean_triple (a ^ 2) (b ^ 2) c,
  { calc ((a ^ 2) * (a ^ 2)) + ((b ^ 2) * (b ^ 2))
        = a ^ 4 + b ^ 4 : by ring
    ... = c ^ 2 : by rw h.1.2.2
    ... = c * c : by rw pow_two
  },
  -- coprime requirement:
  have h2 : int.gcd (a ^ 2) (b ^ 2) = 1,
  { change nat.coprime (int.nat_abs (a ^ 2)) (int.nat_abs (b ^ 2)),
    rw [pow_two, int.nat_abs_mul],
    apply nat.coprime.mul;
    { rw [pow_two, int.nat_abs_mul], apply nat.coprime.mul_right;
      apply (coprime_of_minimal h) } },
  -- in order to reduce the possibilities we get from the classification of pythagorean triples
  -- it helps if we know the parity of a ^ 2 (and the sign of c):
  have ha22 : a ^ 2 % 2 = 1, { rw [pow_two, int.mul_mod, ha2], norm_num },
  obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
    pythagorean_triple.coprime_classification' ht h2 ha22 hc,
  -- Now a, n, m form a pythagorean triple and so we can obtain r and s such that
  -- a = r ^ 2 - s ^ 2, n = 2 * r * s and m = r ^ 2 + s ^ 2
  -- formula:
  have htt : pythagorean_triple a n m,
  { delta pythagorean_triple,
    rw [← pow_two, ← pow_two, ← pow_two], exact (add_eq_of_eq_sub ht1) },
  -- a and n are coprime, because a ^ 2 = m ^ 2 - n ^ 2 and m and n are coprime.
  have h3 : int.gcd a n = 1,
  { have ha : (int.gcd a n : ℤ) ^ 2 ∣ a ^ 2,
    { exact (int.pow_dvd_pow_iff (dec_trivial : 0 < 2)).mpr (int.gcd_dvd_left a n),},
    have hn : (int.gcd a n : ℤ) ^ 2 ∣ n ^ 2,
    { exact (int.pow_dvd_pow_iff (dec_trivial : 0 < 2)).mpr (int.gcd_dvd_right a n),},
    have hm : (int.gcd a n : ℤ) ^ 2 ∣ m ^ 2,
    { rw [← (add_eq_of_eq_sub ht1)], exact dvd_add ha hn },
    replace hm : (int.gcd a n : ℤ) ∣ m, { exact (int.pow_dvd_pow_iff (dec_trivial : 0 < 2)).mp hm},
    apply nat.eq_one_of_dvd_one,
    rw [←ht4], apply int.coe_nat_dvd.mp, exact int.dvd_gcd hm (int.gcd_dvd_right a n) },
  -- m is positive because b is non-zero and b ^ 2 = 2 * m * n and we already have 0 ≤ m.
  have hb20 : b ^ 2 ≠ 0, { exact mt pow_eq_zero h.1.2.1 },
  have h4 : 0 < m,
  { apply lt_of_le_of_ne ht6,
    by_contradiction hm0,
    revert hb20,
    rw [ht2, ← (not_not.mp hm0)], simp },
  obtain ⟨r, s, htt1, htt2, htt3, htt4, htt5, htt6⟩ :=
    pythagorean_triple.coprime_classification' htt h3 ha2 h4,
  -- Now use the fact that (b / 2) ^ 2 = m * r * s, and m, r and s are pairwise coprime to obtain
  -- i, j and k such that m = i ^ 2, r = j ^ 2 and s = k ^ 2.
  -- m and r * s are coprime because m = r ^ 2 + s ^ 2 and r and s are coprime.
  have hcp : int.gcd m (r * s) = 1, exact int.coprime_of_sqr_sum' htt3 htt4,
  -- b is even because b ^ 2 = 2 * m * n.
  have hb2 : 2 ∣ b,
  { apply (or_self _).mp (int.prime.dvd_mul' (by norm_num : nat.prime 2) _),
    rw ← pow_two, rw [ht2, mul_assoc], exact dvd_mul_right 2 (m * n) },
  have hs : (b / 2) ^ 2 = m * (r * s),
  { have hb22 : 2 * (b / 2) = b, { exact int.mul_div_cancel' hb2 },
    apply (mul_right_inj' (by norm_num : (4 : ℤ) ≠ 0)).mp,
    calc 4 * (b / 2) ^ 2 = (2 * (b / 2)) * (2 * (b / 2)) : by ring
                    ... = 2 * m * (2 * r * s) : by rw [hb22, ← pow_two, ht2, htt2]
                    ... = 4 * (m * (r * s)) : by ring },
  have hrsz : r * s ≠ 0, -- because b ^ 2 is not zero and (b / 2) ^ 2 = m * (r * s)
  { by_contradiction hrsz,
    revert hb20, rw [ht2, htt2, mul_assoc, @mul_assoc _ _ _ r s, (not_not.mp hrsz)],
    simp },
  have h2b0 : b / 2 ≠ 0,
  { apply ne_zero_pow (dec_trivial : 2 ≠ 0),
    rw hs, apply mul_ne_zero, { exact ne_of_gt h4}, { exact hrsz } },
  obtain ⟨i, hi⟩ := int.sqr_of_coprime hcp hs.symm,
  -- use m is positive to exclude m = - i ^ 2
  have hi' : ¬ m = - i ^ 2,
  { by_contradiction h1,
    have hit : - i ^ 2 ≤ 0, apply neg_nonpos.mpr (pow_two_nonneg i),
    rw ← h1 at hit,
    apply absurd h4 (not_lt.mpr hit) },
  replace hi : m = i ^ 2, { apply or.resolve_right hi hi' },
  rw mul_comm at hs,
  rw [int.gcd_comm] at hcp,
  -- obtain d such that r * s = d ^ 2
  obtain ⟨d, hd⟩ := int.sqr_of_coprime hcp hs.symm,
  -- (b / 2) ^ 2 and m are positive so r * s is positive
  have hd' : ¬ r * s = - d ^ 2,
  { by_contradiction h1,
    rw h1 at hs,
    have h2 : (b / 2) ^ 2 ≤ 0,
    { rw [hs, (by ring : - d ^ 2 * m = - (d ^ 2 * m))], apply neg_nonpos.mpr,
      apply (zero_le_mul_right h4).mpr (pow_two_nonneg d) },
    have h2' : 0 ≤ (b / 2) ^ 2, { apply pow_two_nonneg (b / 2) },
    exact absurd (lt_of_le_of_ne h2' (ne.symm (pow_ne_zero _ h2b0))) (not_lt.mpr h2) },
  replace hd : r * s = d ^ 2, { apply or.resolve_right hd hd' },
  -- r = +/- j ^ 2
  obtain ⟨j, hj⟩ := int.sqr_of_coprime htt4 hd,
  have hj0 : j ≠ 0,
  { intro h0, rw [h0, zero_pow (dec_trivial : 0 < 2), neg_zero, or_self] at hj,
    apply left_ne_zero_of_mul hrsz hj },
  rw mul_comm at hd,
  rw [int.gcd_comm] at htt4,
  -- s = +/- k ^ 2
  obtain ⟨k, hk⟩ := int.sqr_of_coprime htt4 hd,
  have hk0 : k ≠ 0,
  { intro h0, rw [h0, zero_pow (dec_trivial : 0 < 2), neg_zero, or_self] at hk,
    apply right_ne_zero_of_mul hrsz hk },
  have hj2 : r ^ 2 = j ^ 4, { cases hj with hjp hjp; { rw hjp, ring } },
  have hk2 : s ^ 2 = k ^ 4, { cases hk with hkp hkp; { rw hkp, ring } },
  -- from m = r ^ 2 + s ^ 2 we now get a new solution to a ^ 4 + b ^ 4 = c ^ 2:
  have hh : i ^ 2 = j ^ 4 + k ^ 4, { rw [← hi, htt3, hj2, hk2] },
  have hn : n ≠ 0, { rw ht2 at hb20, apply right_ne_zero_of_mul hb20 },
  -- and it has a smaller c: from c = m ^ 2 + n ^ 2 we see that m is smaller than c, and i ^ 2 = m.
  have hic : int.nat_abs i < int.nat_abs c,
  { apply int.coe_nat_lt.mp, rw ← (int.eq_nat_abs_of_zero_le (le_of_lt hc)),
    apply gt_of_gt_of_ge _ (int.abs_le_self_pow_two i),
    rw [← hi, ht3],
    apply gt_of_gt_of_ge _ (int.le_self_pow_two m),
    exact lt_add_of_pos_right (m ^ 2) (pow_two_pos_of_ne_zero n hn) },
  have hic' : int.nat_abs c ≤ int.nat_abs i,
  { apply (h.2 j k i),
    exact and.intro hj0 (and.intro hk0 hh.symm) },
  apply absurd (not_le_of_lt hic) (not_not.mpr hic')
end

end fermat_42

lemma not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 2 :=
begin
  intro h,
  obtain ⟨a0, b0, c0, ⟨hf, h2, hp⟩⟩ :=
    fermat_42.exists_pos_odd_minimal (and.intro ha (and.intro hb h)),
  apply fermat_42.not_minimal hf h2 hp
end

theorem not_fermat_4 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 4 :=
begin
  intro heq,
  apply @not_fermat_42 _ _ (c ^ 2) ha hb,
  rw heq, ring
end

import tactic
import algebra.big_operators.ring
import data.nat.parity
import data.finset.intervals
import data.padics.padic_norm

open_locale big_operators

open finset

open nat

instance : fact (nat.prime 1979) := by norm_num

open finset

namespace imo1979q1

-- some constants
@[reducible] def a : ℚ := ∑ n in range 1320, (-1)^(n + 1) / n
@[reducible] def b : ℚ := ∑ n in range 1320, 1 / n
@[reducible] def c : ℚ := ∑ n in range 660, 1 / n
@[reducible] def d : ℚ := ∑ n in Ico 660 1320, 1 / n
@[reducible] def e : ℚ := ∑ n in range 330, 1 / (n + 660)
@[reducible] def f : ℚ := ∑ n in range 330, 1 / (1319 - n)

/-
  We start with some lemmas:

  Lemma 1 : b - a = c
  Lemma 2 : c + d = b
  Corollary 3 : a = d
  Lemma 4 : d = e + f

  Then we prove the theorem, by showing the 1979-adic
  valuation of e + f is positive.
-/

@[reducible] def double : ℕ ↪ ℕ := ⟨λ n, 2 * n, λ a b, mul_left_cancel' (by norm_num)⟩

lemma lemma1 : b - a = c :=
  calc b - a = ∑ n in range 1320, (1/n - (-1)^(n+1)/n) : by rw sum_sub_distrib
    ... = ∑ n in range 1320, ite (even n) (2/n) 0 : by {
      apply sum_congr rfl,
      rintros x hx,
      rw [pow_add, pow_one, mul_neg_one, neg_div, sub_neg_eq_add, ← _root_.add_div],
      split_ifs,
      { rcases h with ⟨n, rfl⟩,
        rw [pow_mul, pow_two],
        simp, norm_num },
      { rw not_even_iff at h,
        have h8 := nat.mod_add_div x 2,
        rw h at h8,
        suffices : (1 : ℚ) + (-1)^x = 0,
          rw this, simp,
        rw ← h8,
        simp [pow_add, pow_mul],
      }
    }
    ... = ∑ (x : ℕ) in filter even (range 1320), 2 / x : by rw sum_filter
    ... = ∑ (x : ℕ) in map double (range 660), (2 : ℚ) / x : by {
      apply sum_congr, swap, simp,
      apply finset.subset.antisymm,
      { intros x hx,
        rw mem_filter at hx,
        rcases hx with ⟨hx1, m, rfl⟩,
        rw mem_map,
        use m,
        existsi _, refl,
        rw mem_range at hx1 ⊢,
        linarith },
      { intros x hx,
        rw mem_filter,
        rw mem_map at hx,
        rcases hx with ⟨a, ha, rfl⟩,
        split,
        { rw mem_range at ha ⊢,
          change 2 * a < 1320,
          linarith },
        { existsi a,
          refl
        }
      }
    }
    ... = c : by {
      rw sum_map (range 660) double (λ n, (2 : ℚ) / n),
      apply sum_congr, refl, -- is there a better way?
      intros x hx,
      show (2 : ℚ) / (2 * x : ℕ) = _,
      push_cast,
      change (2 : ℚ) / (2 * x) = 1 / x,
      generalize h : (x : ℚ) = q,
      by_cases hq : q = 0,
        rw hq, ring,
      field_simp [hq] }

lemma lemma2 : c + d = b :=
begin
  unfold c d b,
  simp only [← Ico.zero_bot],
  rw ← sum_union,
  { apply sum_congr,
    { ext x,
      suffices : x < 660 ∨ 660 ≤ x ∧ x < 1320 ↔ x < 1320,
        simpa,
      split,
      { rintro (a | ⟨b, c⟩); linarith },
      { intro hx,
        cases lt_or_le x 660,
        { left, assumption },
        { right, cc } } },
    { intros, refl } },
  apply Ico.disjoint_consecutive
end

lemma corollary3 : a = d :=
begin
  apply add_left_cancel, swap, exact c,
  rw lemma2,
  rw ← lemma1,
  apply sub_add_cancel,
end

lemma lemma4 : e + f = d :=
begin
  unfold d e f,
  rw (Ico.zero_bot 330).symm,
  have h : ∑ (n : ℕ) in Ico 0 330, (1 : ℚ) / (n + 660) =
    ∑ (m : ℕ) in Ico 660 990, (1 : ℚ) / m,
  {
    rw ←Ico.image_add 0 330 660,
    rw sum_image,
    { apply sum_congr, refl,
      intros, simp [add_comm] },
    { intros x hx y hy,
      exact (add_right_inj 660).mp }
  },
  rw h, clear h,
  have h : ∑ (n : ℕ) in Ico 0 330, (1 : ℚ) / (1319 - n) =
    ∑ (m : ℕ) in Ico 990 1320, (1 : ℚ) / m,
  { have h2 : image (λ (j : ℕ), 1319 - j) (Ico 0 330) =
      Ico (990) (1320),
    { rw Ico.image_const_sub, refl, linarith },
    rw ← h2,
    rw sum_image,
    { apply sum_congr, refl,
      intros,
      apply congr_arg,
      rw nat.cast_sub, norm_cast,
      rw Ico.mem at H,
      cases H, linarith },
    { intros x hx y hy,
      intro h,
      rw [Ico.zero_bot, mem_range] at hx hy,
      rw nat.sub_eq_iff_eq_add (show x ≤ 1319, by linarith) at h,
      rw nat.sub_add_eq_add_sub (show y ≤ 1319, by linarith) at h,
      symmetry' at h,
      rw nat.sub_eq_iff_eq_add at h, swap, linarith,
      exact (add_right_inj 1319).mp h }
  },
  rw h, clear h,
  rw ←sum_union,
  { apply sum_congr,
    { apply Ico.union_consecutive; linarith },
    { intros, refl } },
  { apply Ico.disjoint_consecutive }
end

lemma nat.zero_or_one_le (n : ℕ) : n = 0 ∨ 1 ≤ n :=
begin
  cases n,
    left, refl,
  right, exact le_add_left (le_refl 1),
end

lemma nat.le_mul_of_one_le_right {a : ℕ} (b : ℕ) : 1 ≤ a → b ≤ b * a :=
le_mul_of_one_le_right (nat.zero_le _)

--set_option trace.linarith true
lemma nat.not_dvd_of_pos_of_lt {a b : ℕ} (h1 : 0 < b) (h2 : b < a) : ¬ a ∣ b :=
begin
  rintros ⟨c, rfl⟩,
  rcases nat.zero_or_one_le c with (rfl | hc),
  { exact lt_irrefl 0 h1 },
  { exact not_lt.2 (nat.le_mul_of_one_le_right _ hc) h2 },
end

lemma easy1 {n : ℕ} (hn : n < 330) : padic_val_rat 1979 (n + 660) = 0 :=
begin
  rw (show (n : ℚ) + 660 = (n + 660 : ℕ), by norm_num),
  rw ← padic_val_rat_of_nat,
  norm_cast,
  apply padic_val_nat_of_not_dvd,
  apply nat.not_dvd_of_pos_of_lt; linarith,
end

lemma easy2 {n : ℕ} (hn : n < 330) : padic_val_rat 1979 (1319 - n) = 0 :=
begin
  have h : (1319 : ℚ) - n = (1319 - n : ℕ),
    rw nat.cast_sub,
    { norm_cast },
    { linarith },
  rw h,
  rw ← padic_val_rat_of_nat,
  norm_cast,
  apply padic_val_nat_of_not_dvd,
  apply nat.not_dvd_of_pos_of_lt,
    apply nat.sub_pos_of_lt, linarith,
  rw nat.sub_lt_right_iff_lt_add; linarith,
end


lemma lemma5 : ∀ n ∈ range 330, padic_val_rat 1979 ((1 / (n + 660) + 1 / (1319 - n)) : ℚ) = 1 :=
begin
  intros n hn,
  rw mem_range at hn,
  have h1 : (n : ℚ) + 660 ≠ 0,
    apply ne_of_gt,
    norm_cast, simp,
  have h2 : (1319 : ℚ) - n ≠ 0,
    have h3 : (n : ℚ) < 330, norm_cast, exact hn,
    linarith,
  have h2' : 0 ≤ (1319 : ℤ) - n,
    have h3 : (n : ℤ) < 330, norm_cast, exact hn,
    linarith,
  have h3 : (1 : ℚ) / (n + 660) + 1 / (1319 - n) = 1979 / ((n + 660) * (1319 - n)),
    field_simp [h1, h2],
    generalize : (n : ℚ) = q,
    ring,
  rw h3, clear h3,
  rw padic_val_rat.div 1979 (show (1979 : ℚ) ≠ 0, by norm_num) (mul_ne_zero h1 h2),
  have h := padic_val_rat.padic_val_rat_self (show 1 < 1979, by norm_num),
  rw (show ((1979 : ℕ) : ℚ) = 1979, by norm_cast) at h,
  rw h,
  suffices : 0 = padic_val_rat 1979 ((↑n + 660) * (1319 - ↑n)),
    linarith,
  rw padic_val_rat.mul 1979 h1 h2,
  rw [easy1 hn, easy2 hn],
  simp,
end

theorem imo1979_q1 (p q : ℕ) (hq : 0 < q) : (p : ℚ) / q =
-- 1 - (1/2) + (1/3) - (1/4) + ... + (1/1319),
∑ n in finset.range 1320, (-1)^(n + 1) / n
→ 1979 ∣ p :=
begin
  change _ = a → _,
  rw corollary3,
  rw ← lemma4,
  intro h,
  unfold e f at h,
  rw ← sum_add_distrib at h,
  rcases nat.zero_or_one_le p with (rfl | hp),
    simp,
  suffices : 0 < padic_val_rat 1979 p,
  { rw ← padic_val_rat_of_nat at this,
    have h2 : 0 < padic_val_nat 1979 p,
      assumption_mod_cast,
    exact dvd_of_one_le_padic_val_nat h2 },
  have hp' : (p : ℚ) ≠ 0,
  { intro hp2,
    have hp3 : p = 0,
    assumption_mod_cast,
    subst hp3,
    exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp) },
  have hq' : (q : ℚ) ≠ 0,
  { intro hq2,
    have hq3 : q = 0,
    assumption_mod_cast,
    subst hq3,
    exact lt_irrefl 0 hq },
  suffices : 0 < padic_val_rat 1979 (p / q),
  { rw [padic_val_rat.div 1979 hp' hq', ← padic_val_rat_of_nat _ q] at this,
    apply lt_of_lt_of_le this,
    apply sub_le_self,
    norm_cast, simp },
  rw h,
  apply padic_val_rat.sum_pos_of_pos,
  { intros i hi,
    rw lemma5 i (mem_range.2 hi),
    exact zero_lt_one },
  { rw ← h,
    exact div_ne_zero hp' hq' }
end

end imo1979q1

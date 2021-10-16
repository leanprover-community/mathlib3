/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.modeq
import tactic.ring

/-!

# Congruences modulo an integer

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`data.nat.modeq` defines them for the natural numbers. The notation is short for `n.modeq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/

namespace int

/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
@[derive decidable]
def modeq (n a b : ℤ) := a % n = b % n

notation a ` ≡ `:50 b ` [ZMOD `:50 n `]`:0 := modeq n a b

variables {m n a b c d : ℤ}

namespace modeq

@[refl] protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] := @rfl _ _

protected theorem rfl : a ≡ a [ZMOD n] := modeq.refl _

@[symm] protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] := eq.symm

@[trans] protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] := eq.trans

end modeq

lemma coe_nat_modeq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] :=
by unfold modeq nat.modeq; rw ← int.coe_nat_eq_coe_nat_iff; simp [coe_nat_mod]

theorem modeq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a :=
by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

lemma _root_.has_dvd.dvd.modeq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] := modeq_zero_iff_dvd.2 h
lemma _root_.has_dvd.dvd.zero_modeq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] := h.modeq_zero_int.symm

theorem modeq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a :=
by rw [modeq, eq_comm];
   simp [mod_eq_mod_iff_mod_sub_eq_zero, dvd_iff_mod_eq_zero, -euclidean_domain.mod_eq_zero]

theorem modeq.dvd : a ≡ b [ZMOD n] → n ∣ b - a := modeq_iff_dvd.1
theorem modeq_of_dvd : n ∣ b - a → a ≡ b [ZMOD n] := modeq_iff_dvd.2

theorem mod_modeq (a n) : a % n ≡ a [ZMOD n] := mod_mod _ _

namespace modeq

protected theorem modeq_of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
modeq_iff_dvd.2 $ d.trans h.dvd

protected theorem mul_left' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD (c * n)] :=
or.cases_on hc.lt_or_eq (λ hc,
  by unfold modeq;
  simp [mul_mod_mul_of_pos hc, (show _ = _, from h)] )
(λ hc, by simp [hc.symm])

protected theorem mul_right' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD (n * c)] :=
by rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left' hc

protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
modeq_iff_dvd.2 $ by { convert dvd_add h₁.dvd h₂.dvd, ring }

protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
modeq.rfl.add h

protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
h.add modeq.rfl

protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
  c ≡ d [ZMOD n] :=
have d - c = b + d - (a + c) - (b - a) := by ring,
modeq_iff_dvd.2 $ by { rw [this], exact dvd_sub h₂.dvd h₁.dvd }

protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
modeq.rfl.add_left_cancel h

protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
  a ≡ b [ZMOD n] :=
by { rw [add_comm a, add_comm b] at h₂, exact h₁.add_left_cancel h₂ }

protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
modeq.rfl.add_right_cancel h

protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
h.add_left_cancel (by simp_rw [←sub_eq_add_neg, sub_self])

protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
  a - c ≡ b - d [ZMOD n] :=
by { rw [sub_eq_add_neg, sub_eq_add_neg], exact h₁.add h₂.neg }

protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
modeq.rfl.sub h

protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
h.sub modeq.rfl

protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
or.cases_on (le_total 0 c)
(λ hc, (h.mul_left' hc).modeq_of_dvd (dvd_mul_left _ _) )
(λ hc, by rw [← neg_neg c, ← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul _ b];
    exact ((h.mul_left' $ neg_nonneg.2 hc).modeq_of_dvd (dvd_mul_left _ _)).neg)

protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
by { rw [mul_comm a, mul_comm b], exact h.mul_left c }

protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
(h₂.mul_left _).trans (h₁.mul_right _)

protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] :=
begin
  induction m with d hd, {refl},
  rw [pow_succ, pow_succ],
  exact h.mul hd,
end

theorem of_modeq_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] :=
by rw [modeq_iff_dvd] at *; exact (dvd_mul_left n m).trans h

theorem of_modeq_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
mul_comm m n ▸ of_modeq_mul_left _

end modeq

theorem modeq_one : a ≡ b [ZMOD 1] := modeq_of_dvd (one_dvd _)

lemma modeq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
(modeq_of_dvd dvd_rfl).symm

lemma modeq_and_modeq_iff_modeq_mul {a b m n : ℤ} (hmn : m.nat_abs.coprime n.nat_abs) :
  a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ (a ≡ b [ZMOD m * n]) :=
⟨λ h, begin
    rw [modeq_iff_dvd, modeq_iff_dvd] at h,
    rw [modeq_iff_dvd, ← nat_abs_dvd, ← dvd_nat_abs,
      coe_nat_dvd, nat_abs_mul],
    refine hmn.mul_dvd_of_dvd_of_dvd _ _;
    rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs]; tauto
  end,
λ h, ⟨h.of_modeq_mul_right _, h.of_modeq_mul_left _⟩⟩

lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * nat.gcd_a a b ≡ nat.gcd a b [ZMOD b] :=
by { rw [← add_zero ((a : ℤ) * _), nat.gcd_eq_gcd_ab],
  exact (dvd_mul_right _ _).zero_modeq_int.add_left _ }

theorem modeq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a + n*c ≡ b [ZMOD n] :=
calc a + n*c ≡ b + n*c [ZMOD n] : ha.add_right _
         ... ≡ b + 0 [ZMOD n] : (dvd_mul_right _ _).modeq_zero_int.add_left _
         ... ≡ b [ZMOD n] : by rw add_zero

lemma mod_coprime {a b : ℕ} (hab : nat.coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
⟨ nat.gcd_a a b,
  have hgcd : nat.gcd a b = 1, from nat.coprime.gcd_eq_one hab,
  calc
   ↑a * nat.gcd_a a b ≡ ↑a * nat.gcd_a a b + ↑b * nat.gcd_b a b [ZMOD ↑b] : modeq.symm $
                      modeq_add_fac _ $ modeq.refl _
              ... ≡ 1 [ZMOD ↑b] : by rw [← nat.gcd_eq_gcd_ab, hgcd]; reflexivity ⟩

lemma exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
⟨ a % b, mod_nonneg _ (ne_of_gt hb),
  have a % b < |b|, from mod_lt _ (ne_of_gt hb),
  by rwa abs_of_pos hb at this,
  by simp [modeq] ⟩

lemma exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
let ⟨z, hz1, hz2, hz3⟩ := exists_unique_equiv a hb in
⟨z.nat_abs, by split; rw [←of_nat_eq_coe, of_nat_nat_abs_eq_of_nonneg hz1]; assumption⟩


@[simp] lemma mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
(mod_modeq _ _).of_modeq_mul_right _

@[simp] lemma mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
(mod_modeq _ _).of_modeq_mul_left _

end int

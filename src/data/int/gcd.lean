/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
import data.nat.prime
/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcd_a x y` and `gcd_b x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcd_a x y + y * gcd_b x y`.

-/

/-! ### Extended Euclidean algorithm -/
namespace nat

/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
def xgcd_aux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
| 0          s t r' s' t' := (r', s', t')
| r@(succ _) s t r' s' t' :=
  have r' % r < r, from mod_lt _ $ succ_pos _,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp] theorem xgcd_zero_left {s t r' s' t'} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by simp [xgcd_aux]

theorem xgcd_aux_rec {r s t r' s' t'} (h : 0 < r) :
  xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
by cases r; [exact absurd h (lt_irrefl _), {simp only [xgcd_aux], refl}]

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : ℕ) : ℤ × ℤ := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x y : ℕ) : ℤ := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x y : ℕ) : ℤ := (xgcd x y).2

@[simp] theorem xgcd_aux_fst (x y) : ∀ s t s' t',
  (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y (by simp) (λ x y h IH s t s' t', by simp [xgcd_aux_rec, h, IH]; rw ← gcd_rec)

theorem xgcd_aux_val (x y) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1]; cases xgcd_aux x 1 0 y 0 1; refl

theorem xgcd_val (x y) : xgcd x y = (gcd_a x y, gcd_b x y) :=
by unfold gcd_a gcd_b; cases xgcd x y; refl

section
parameters (x y : ℕ)

private def P : ℕ × ℤ × ℤ → Prop
| (r, s, t) := (r : ℤ) = x * s + y * t

theorem xgcd_aux_P {r r'} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') →
  P (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by simp) $ λ a b h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, dsimp [P] at *,
  rw [int.mod_def], generalize : (b / a : ℤ) = k,
  rw [p, p'],
  simp [mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, sub_eq_neg_add, mul_assoc]
end

/-- Bézout's lemma: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcd_a x y + y * gcd_b x y :=
by have := @xgcd_aux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P]);
   rwa [xgcd_aux_val, xgcd_val] at this
end

end nat

/-! ### Divisibility over ℤ -/
namespace int

theorem nat_abs_div (a b : ℤ) (H : b ∣ a) : nat_abs (a / b) = (nat_abs a) / (nat_abs b) :=
begin
  cases (nat.eq_zero_or_pos (nat_abs b)),
  {rw eq_zero_of_nat_abs_eq_zero h, simp [int.div_zero]},
  calc
  nat_abs (a / b) = nat_abs (a / b) * 1 : by rw mul_one
    ... = nat_abs (a / b) * (nat_abs b / nat_abs b) : by rw nat.div_self h
    ... = nat_abs (a / b) * nat_abs b / nat_abs b : by rw (nat.mul_div_assoc _ (dvd_refl _))
    ... = nat_abs (a / b * b) / nat_abs b : by rw (nat_abs_mul (a / b) b)
    ... = nat_abs a / nat_abs b : by rw int.div_mul_cancel H,
end

theorem nat_abs_dvd_abs_iff {i j : ℤ} : i.nat_abs ∣ j.nat_abs ↔ i ∣ j :=
⟨assume (H : i.nat_abs ∣ j.nat_abs), dvd_nat_abs.mp (nat_abs_dvd.mp (coe_nat_dvd.mpr H)),
assume H : (i ∣ j), coe_nat_dvd.mp (dvd_nat_abs.mpr (nat_abs_dvd.mpr H))⟩

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : nat.prime p) {m n : ℤ} {k l : ℕ}
      (hpm : ↑(p ^ k) ∣ m)
      (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k+l+1)) ∣ m*n) : ↑(p ^ (k+1)) ∣ m ∨ ↑(p ^ (l+1)) ∣ n :=
have hpm' : p ^ k ∣ m.nat_abs, from int.coe_nat_dvd.1 $ int.dvd_nat_abs.2 hpm,
have hpn' : p ^ l ∣ n.nat_abs, from int.coe_nat_dvd.1 $ int.dvd_nat_abs.2 hpn,
have hpmn' : (p ^ (k+l+1)) ∣ m.nat_abs*n.nat_abs,
  by rw ←int.nat_abs_mul; apply (int.coe_nat_dvd.1 $ int.dvd_nat_abs.2 hpmn),
let hsd := nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn' in
hsd.elim
  (λ hsd1, or.inl begin apply int.dvd_nat_abs.1, apply int.coe_nat_dvd.2 hsd1 end)
  (λ hsd2, or.inr begin apply int.dvd_nat_abs.1, apply int.coe_nat_dvd.2 hsd2 end)

theorem dvd_of_mul_dvd_mul_left {i j k : ℤ} (k_non_zero : k ≠ 0) (H : k * i ∣ k * j) : i ∣ j :=
dvd.elim H (λl H1, by rw mul_assoc at H1; exact ⟨_, mul_left_cancel' k_non_zero H1⟩)

theorem dvd_of_mul_dvd_mul_right {i j k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) : i ∣ j :=
by rw [mul_comm i k, mul_comm j k] at H; exact dvd_of_mul_dvd_mul_left k_non_zero H

lemma prime.dvd_nat_abs_of_coe_dvd_pow_two {p : ℕ} (hp : p.prime) (k : ℤ) (h : ↑p ∣ k ^ 2) :
  p ∣ k.nat_abs :=
begin
  apply @nat.prime.dvd_of_dvd_pow _ _ 2 hp,
  rwa [pow_two, ← nat_abs_mul, ← coe_nat_dvd_left, ← pow_two]
end

end int

lemma pow_gcd_eq_one {M : Type*} [monoid M] (x : M) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) :
  x ^ m.gcd n = 1 :=
begin
  cases m, { simp only [hn, nat.gcd_zero_left] },
  obtain ⟨x, rfl⟩ : is_unit x,
  { apply is_unit_of_pow_eq_one _ _ hm m.succ_pos },
  simp only [← units.coe_pow] at *,
  rw [← units.coe_one, ← gpow_coe_nat, ← units.ext_iff] at *,
  simp only [nat.gcd_eq_gcd_ab, gpow_add, gpow_mul, hm, hn, one_gpow, one_mul]
end

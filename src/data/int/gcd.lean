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

## Tags

Bézout's lemma, Bezout's lemma
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

@[simp] theorem gcd_a_zero_left {s : ℕ} : gcd_a 0 s = 0 :=
by { unfold gcd_a, rw [xgcd, xgcd_zero_left] }

@[simp] theorem gcd_b_zero_left {s : ℕ} : gcd_b 0 s = 1 :=
by { unfold gcd_b, rw [xgcd, xgcd_zero_left] }

@[simp] theorem gcd_a_zero_right {s : ℕ} (h : s ≠ 0) : gcd_a s 0 = 1 :=
begin
  unfold gcd_a xgcd,
  induction s,
  { exact absurd rfl h, },
  { simp [xgcd_aux], }
end

@[simp] theorem gcd_b_zero_right {s : ℕ} (h : s ≠ 0) : gcd_b s 0 = 0 :=
begin
  unfold gcd_b xgcd,
  induction s,
  { exact absurd rfl h, },
  { simp [xgcd_aux], }
end

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

/-- **Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcd_a x y + y * gcd_b x y :=
by have := @xgcd_aux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P]);
   rwa [xgcd_aux_val, xgcd_val] at this
end

lemma exists_mul_mod_eq_gcd {k n : ℕ} (hk : gcd n k < k) :
  ∃ m, n * m % k = gcd n k :=
begin
  have hk' := int.coe_nat_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt (zero_le (gcd n k)) hk)),
  have key := congr_arg (λ m, int.nat_mod m k) (gcd_eq_gcd_ab n k),
  simp_rw int.nat_mod at key,
  rw [int.add_mul_mod_self_left, ←int.coe_nat_mod, int.to_nat_coe_nat, mod_eq_of_lt hk] at key,
  refine ⟨(n.gcd_a k % k).to_nat, eq.trans (int.coe_nat_inj _) key.symm⟩,
  rw [int.coe_nat_mod, int.coe_nat_mul, int.to_nat_of_nonneg (int.mod_nonneg _ hk'),
      int.to_nat_of_nonneg (int.mod_nonneg _ hk'), int.mul_mod, int.mod_mod, ←int.mul_mod],
end

lemma exists_mul_mod_eq_one_of_coprime {k n : ℕ} (hkn : coprime n k) (hk : 1 < k) :
  ∃ m, n * m % k = 1 :=
Exists.cases_on (exists_mul_mod_eq_gcd (lt_of_le_of_lt (le_of_eq hkn) hk))
  (λ m hm, ⟨m, hm.trans hkn⟩)

end nat

/-! ### Divisibility over ℤ -/
namespace int

protected lemma coe_nat_gcd (m n : ℕ) : int.gcd ↑m ↑n = nat.gcd m n := rfl

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a : ℤ → ℤ → ℤ
| (of_nat m) n := m.gcd_a n.nat_abs
| -[1+ m]    n := -m.succ.gcd_a n.nat_abs

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b : ℤ → ℤ → ℤ
| m (of_nat n) := m.nat_abs.gcd_b n
| m -[1+ n]    := -m.nat_abs.gcd_b n.succ

/-- **Bézout's lemma** -/
theorem gcd_eq_gcd_ab : ∀ x y : ℤ, (gcd x y : ℤ) = x * gcd_a x y + y * gcd_b x y
| (m : ℕ) (n : ℕ) := nat.gcd_eq_gcd_ab _ _
| (m : ℕ) -[1+ n] := show (_ : ℤ) = _ + -(n+1) * -_, by rw neg_mul_neg; apply nat.gcd_eq_gcd_ab
| -[1+ m] (n : ℕ) := show (_ : ℤ) = -(m+1) * -_ + _ , by rw neg_mul_neg; apply nat.gcd_eq_gcd_ab
| -[1+ m] -[1+ n] := show (_ : ℤ) = -(m+1) * -_ + -(n+1) * -_,
  by { rw [neg_mul_neg, neg_mul_neg], apply nat.gcd_eq_gcd_ab }

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

lemma prime.dvd_nat_abs_of_coe_dvd_sq {p : ℕ} (hp : p.prime) (k : ℤ) (h : ↑p ∣ k ^ 2) :
  p ∣ k.nat_abs :=
begin
  apply @nat.prime.dvd_of_dvd_pow _ _ 2 hp,
  rwa [sq, ← nat_abs_mul, ← coe_nat_dvd_left, ← sq]
end

/-- ℤ specific version of least common multiple. -/
def lcm (i j : ℤ) : ℕ := nat.lcm (nat_abs i) (nat_abs j)

theorem lcm_def (i j : ℤ) : lcm i j = nat.lcm (nat_abs i) (nat_abs j) := rfl

protected lemma coe_nat_lcm (m n : ℕ) : int.lcm ↑m ↑n = nat.lcm m n := rfl

theorem gcd_dvd_left (i j : ℤ) : (gcd i j : ℤ) ∣ i :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_left _ _

theorem gcd_dvd_right (i j : ℤ) : (gcd i j : ℤ) ∣ j :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_right _ _

theorem dvd_gcd {i j k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ gcd i j :=
nat_abs_dvd.1 $ coe_nat_dvd.2 $ nat.dvd_gcd (nat_abs_dvd_abs_iff.2 h1) (nat_abs_dvd_abs_iff.2 h2)

theorem gcd_mul_lcm (i j : ℤ) : gcd i j * lcm i j = nat_abs (i * j) :=
by rw [int.gcd, int.lcm, nat.gcd_mul_lcm, nat_abs_mul]

theorem gcd_comm (i j : ℤ) : gcd i j = gcd j i := nat.gcd_comm _ _

theorem gcd_assoc (i j k : ℤ) : gcd (gcd i j) k = gcd i (gcd j k) := nat.gcd_assoc _ _ _

@[simp] theorem gcd_self (i : ℤ) : gcd i i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_left (i : ℤ) : gcd 0 i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_right (i : ℤ) : gcd i 0 = nat_abs i := by simp [gcd]

@[simp] theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 := nat.gcd_one_left _

@[simp] theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 := nat.gcd_one_right _

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = nat_abs i * gcd j k :=
by { rw [int.gcd, int.gcd, nat_abs_mul, nat_abs_mul], apply nat.gcd_mul_left }

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * nat_abs j :=
by { rw [int.gcd, int.gcd, nat_abs_mul, nat_abs_mul], apply nat.gcd_mul_right }

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : 0 < gcd i j :=
nat.gcd_pos_of_pos_left (nat_abs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : 0 < gcd i j :=
nat.gcd_pos_of_pos_right (nat_abs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem gcd_eq_zero_iff {i j : ℤ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
begin
  rw int.gcd,
  split,
  { intro h,
    exact ⟨nat_abs_eq_zero.mp (nat.eq_zero_of_gcd_eq_zero_left h),
      nat_abs_eq_zero.mp (nat.eq_zero_of_gcd_eq_zero_right h)⟩ },
  { intro h, rw [nat_abs_eq_zero.mpr h.left, nat_abs_eq_zero.mpr h.right],
    apply nat.gcd_zero_left }
end

theorem gcd_div {i j k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) :
  gcd (i / k) (j / k) = gcd i j / nat_abs k :=
by rw [gcd, nat_abs_div i k H1, nat_abs_div j k H2];
exact nat.gcd_div (nat_abs_dvd_abs_iff.mpr H1) (nat_abs_dvd_abs_iff.mpr H2)

theorem gcd_div_gcd_div_gcd {i j : ℤ} (H : 0 < gcd i j) :
  gcd (i / gcd i j) (j / gcd i j) = 1 :=
begin
  rw [gcd_div (gcd_dvd_left i j) (gcd_dvd_right i j)],
  rw [nat_abs_of_nat, nat.div_self H]
end

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
int.coe_nat_dvd.1 $ dvd_gcd ((gcd_dvd_left i j).trans H) (gcd_dvd_right i j)

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
int.coe_nat_dvd.1 $ dvd_gcd (gcd_dvd_left j i) ((gcd_dvd_right j i).trans H)

theorem gcd_dvd_gcd_mul_left (i j k : ℤ) : gcd i j ∣ gcd (k * i) j :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (i j k : ℤ) : gcd i j ∣ gcd (i * k) j :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (i j k : ℤ) : gcd i j ∣ gcd i (k * j) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (i j k : ℤ) : gcd i j ∣ gcd i (j * k) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)

theorem gcd_eq_left {i j : ℤ} (H : i ∣ j) : gcd i j = nat_abs i :=
nat.dvd_antisymm (by unfold gcd; exact nat.gcd_dvd_left _ _)
                 (by unfold gcd; exact nat.dvd_gcd (dvd_refl _) (nat_abs_dvd_abs_iff.mpr H))

theorem gcd_eq_right {i j : ℤ} (H : j ∣ i) : gcd i j = nat_abs j :=
by rw [gcd_comm, gcd_eq_left H]

theorem ne_zero_of_gcd {x y : ℤ}
  (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 :=
begin
  contrapose! hc,
  rw [hc.left, hc.right, gcd_zero_right, nat_abs_zero]
end

theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
  ∃ (m' n' : ℤ), gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
⟨_, _, gcd_div_gcd_div_gcd H,
  (int.div_mul_cancel (gcd_dvd_left m n)).symm,
  (int.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
  ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
let ⟨m', n', h⟩ := exists_gcd_one H in ⟨_, m', n', H, h⟩

theorem pow_dvd_pow_iff {m n : ℤ} {k : ℕ} (k0 : 0 < k) : m ^ k ∣ n ^ k ↔ m ∣ n :=
begin
  refine ⟨λ h, _, λ h, pow_dvd_pow_of_dvd h _⟩,
  apply int.nat_abs_dvd_abs_iff.mp,
  apply (nat.pow_dvd_pow_iff k0).mp,
  rw [← int.nat_abs_pow, ← int.nat_abs_pow],
  exact int.nat_abs_dvd_abs_iff.mpr h
end

/-! ### lcm -/

theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i :=
by { rw [int.lcm, int.lcm], exact nat.lcm_comm _ _ }

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) :=
by { rw [int.lcm, int.lcm, int.lcm, int.lcm, nat_abs_of_nat, nat_abs_of_nat], apply nat.lcm_assoc }

@[simp] theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 :=
by { rw [int.lcm], apply nat.lcm_zero_left }

@[simp] theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 :=
by { rw [int.lcm], apply nat.lcm_zero_right }

@[simp] theorem lcm_one_left (i : ℤ) : lcm 1 i = nat_abs i :=
by { rw int.lcm, apply nat.lcm_one_left }

@[simp] theorem lcm_one_right (i : ℤ) : lcm i 1 = nat_abs i :=
by { rw int.lcm, apply nat.lcm_one_right }

@[simp] theorem lcm_self (i : ℤ) : lcm i i = nat_abs i :=
by { rw int.lcm, apply nat.lcm_self }

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j :=
by { rw int.lcm, apply coe_nat_dvd_right.mpr, apply nat.dvd_lcm_left }

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j :=
by { rw int.lcm, apply coe_nat_dvd_right.mpr, apply nat.dvd_lcm_right }

theorem lcm_dvd {i j k : ℤ}  : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k :=
begin
  rw int.lcm,
  intros hi hj,
  exact coe_nat_dvd_left.mpr
    (nat.lcm_dvd (nat_abs_dvd_abs_iff.mpr hi) (nat_abs_dvd_abs_iff.mpr hj))
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

lemma gcd_nsmul_eq_zero {M : Type*} [add_monoid M] (x : M) {m n : ℕ} (hm : m • x = 0)
  (hn : n • x = 0) : (m.gcd n) • x = 0 :=
begin
  apply multiplicative.of_add.injective,
  rw [of_add_nsmul, of_add_zero, pow_gcd_eq_one];
  rwa [←of_add_nsmul, ←of_add_zero, equiv.apply_eq_iff_eq]
end

/-! ### GCD prover -/

namespace tactic
namespace norm_num
open norm_num

lemma int_gcd_helper' {d : ℕ} {x y a b : ℤ} (h₁ : (d:ℤ) ∣ x) (h₂ : (d:ℤ) ∣ y)
  (h₃ : x * a + y * b = d) : int.gcd x y = d :=
begin
  refine nat.dvd_antisymm _ (int.coe_nat_dvd.1 (int.dvd_gcd h₁ h₂)),
  rw [← int.coe_nat_dvd, ← h₃],
  apply dvd_add,
  { exact dvd_mul_of_dvd_left (int.gcd_dvd_left _ _) _ },
  { exact dvd_mul_of_dvd_left (int.gcd_dvd_right _ _) _ }
end

lemma nat_gcd_helper_dvd_left (x y a : ℕ) (h : x * a = y) : nat.gcd x y = x :=
nat.gcd_eq_left ⟨a, h.symm⟩

lemma nat_gcd_helper_dvd_right (x y a : ℕ) (h : y * a = x) : nat.gcd x y = y :=
nat.gcd_eq_right ⟨a, h.symm⟩

lemma nat_gcd_helper_2 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y)
  (hx : x * a = tx) (hy : y * b = ty) (h : ty + d = tx) : nat.gcd x y = d :=
begin
  rw ← int.coe_nat_gcd, apply @int_gcd_helper' _ _ _ a (-b)
    (int.coe_nat_dvd.2 ⟨_, hu.symm⟩) (int.coe_nat_dvd.2 ⟨_, hv.symm⟩),
  rw [mul_neg_eq_neg_mul_symm, ← sub_eq_add_neg, sub_eq_iff_eq_add'],
  norm_cast, rw [hx, hy, h]
end

lemma nat_gcd_helper_1 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y)
  (hx : x * a = tx) (hy : y * b = ty) (h : tx + d = ty) : nat.gcd x y = d :=
(nat.gcd_comm _ _).trans $ nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ hv hu hy hx h

lemma nat_lcm_helper (x y d m n : ℕ) (hd : nat.gcd x y = d) (d0 : 0 < d)
  (xy : x * y = n) (dm : d * m = n) : nat.lcm x y = m :=
(nat.mul_right_inj d0).1 $ by rw [dm, ← xy, ← hd, nat.gcd_mul_lcm]

lemma nat_coprime_helper_zero_left (x : ℕ) (h : 1 < x) : ¬ nat.coprime 0 x :=
mt (nat.coprime_zero_left _).1 $ ne_of_gt h

lemma nat_coprime_helper_zero_right (x : ℕ) (h : 1 < x) : ¬ nat.coprime x 0 :=
mt (nat.coprime_zero_right _).1 $ ne_of_gt h

lemma nat_coprime_helper_1 (x y a b tx ty : ℕ)
  (hx : x * a = tx) (hy : y * b = ty) (h : tx + 1 = ty) : nat.coprime x y :=
nat_gcd_helper_1 _ _ _ _ _ _ _ _ _ (one_mul _) (one_mul _) hx hy h

lemma nat_coprime_helper_2 (x y a b tx ty : ℕ)
  (hx : x * a = tx) (hy : y * b = ty) (h : ty + 1 = tx) : nat.coprime x y :=
nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ (one_mul _) (one_mul _) hx hy h

lemma nat_not_coprime_helper (d x y u v : ℕ) (hu : d * u = x) (hv : d * v = y)
  (h : 1 < d) : ¬ nat.coprime x y :=
nat.not_coprime_of_dvd_of_dvd h ⟨_, hu.symm⟩ ⟨_, hv.symm⟩

lemma int_gcd_helper (x y : ℤ) (nx ny d : ℕ) (hx : (nx:ℤ) = x) (hy : (ny:ℤ) = y)
  (h : nat.gcd nx ny = d) : int.gcd x y = d :=
by rwa [← hx, ← hy, int.coe_nat_gcd]

lemma int_gcd_helper_neg_left (x y : ℤ) (d : ℕ) (h : int.gcd x y = d) : int.gcd (-x) y = d :=
by rw int.gcd at h ⊢; rwa int.nat_abs_neg

lemma int_gcd_helper_neg_right (x y : ℤ) (d : ℕ) (h : int.gcd x y = d) : int.gcd x (-y) = d :=
by rw int.gcd at h ⊢; rwa int.nat_abs_neg

lemma int_lcm_helper (x y : ℤ) (nx ny d : ℕ) (hx : (nx:ℤ) = x) (hy : (ny:ℤ) = y)
  (h : nat.lcm nx ny = d) : int.lcm x y = d :=
by rwa [← hx, ← hy, int.coe_nat_lcm]

lemma int_lcm_helper_neg_left (x y : ℤ) (d : ℕ) (h : int.lcm x y = d) : int.lcm (-x) y = d :=
by rw int.lcm at h ⊢; rwa int.nat_abs_neg

lemma int_lcm_helper_neg_right (x y : ℤ) (d : ℕ) (h : int.lcm x y = d) : int.lcm x (-y) = d :=
by rw int.lcm at h ⊢; rwa int.nat_abs_neg

/-- Evaluates the `nat.gcd` function. -/
meta def prove_gcd_nat (c : instance_cache) (ex ey : expr) :
  tactic (instance_cache × expr × expr) := do
  x ← ex.to_nat,
  y ← ey.to_nat,
  match x, y with
  | 0, _ := pure (c, ey, `(nat.gcd_zero_left).mk_app [ey])
  | _, 0 := pure (c, ex, `(nat.gcd_zero_right).mk_app [ex])
  | 1, _ := pure (c, `(1:ℕ), `(nat.gcd_one_left).mk_app [ey])
  | _, 1 := pure (c, `(1:ℕ), `(nat.gcd_one_right).mk_app [ex])
  | _, _ := do
    let (d, a, b) := nat.xgcd_aux x 1 0 y 0 1,
    if d = x then do
      (c, ea) ← c.of_nat (y / x),
      (c, _, p) ← prove_mul_nat c ex ea,
      pure (c, ex, `(nat_gcd_helper_dvd_left).mk_app [ex, ey, ea, p])
    else if d = y then do
      (c, ea) ← c.of_nat (x / y),
      (c, _, p) ← prove_mul_nat c ey ea,
      pure (c, ey, `(nat_gcd_helper_dvd_right).mk_app [ex, ey, ea, p])
    else do
      (c, ed) ← c.of_nat d,
      (c, ea) ← c.of_nat a.nat_abs,
      (c, eb) ← c.of_nat b.nat_abs,
      (c, eu) ← c.of_nat (x / d),
      (c, ev) ← c.of_nat (y / d),
      (c, _, pu) ← prove_mul_nat c ed eu,
      (c, _, pv) ← prove_mul_nat c ed ev,
      (c, etx, px) ← prove_mul_nat c ex ea,
      (c, ety, py) ← prove_mul_nat c ey eb,
      (c, p) ← if a ≥ 0 then prove_add_nat c ety ed etx else prove_add_nat c etx ed ety,
      let pf : expr := if a ≥ 0 then `(nat_gcd_helper_2) else `(nat_gcd_helper_1),
      pure (c, ed, pf.mk_app [ed, ex, ey, ea, eb, eu, ev, etx, ety, pu, pv, px, py, p])
  end

/-- Evaluates the `nat.lcm` function. -/
meta def prove_lcm_nat (c : instance_cache) (ex ey : expr) :
  tactic (instance_cache × expr × expr) := do
  x ← ex.to_nat,
  y ← ey.to_nat,
  match x, y with
  | 0, _ := pure (c, `(0:ℕ), `(nat.lcm_zero_left).mk_app [ey])
  | _, 0 := pure (c, `(0:ℕ), `(nat.lcm_zero_right).mk_app [ex])
  | 1, _ := pure (c, ey, `(nat.lcm_one_left).mk_app [ey])
  | _, 1 := pure (c, ex, `(nat.lcm_one_right).mk_app [ex])
  | _, _ := do
    (c, ed, pd) ← prove_gcd_nat c ex ey,
    (c, p0) ← prove_pos c ed,
    (c, en, xy) ← prove_mul_nat c ex ey,
    d ← ed.to_nat,
    (c, em) ← c.of_nat ((x * y) / d),
    (c, _, dm) ← prove_mul_nat c ed em,
    pure (c, em, `(nat_lcm_helper).mk_app [ex, ey, ed, em, en, pd, p0, xy, dm])
  end

/-- Evaluates the `int.gcd` function. -/
meta def prove_gcd_int (zc nc : instance_cache) : expr → expr →
  tactic (instance_cache × instance_cache × expr × expr)
| x y := match match_neg x with
  | some x := do
    (zc, nc, d, p) ← prove_gcd_int x y,
    pure (zc, nc, d, `(int_gcd_helper_neg_left).mk_app [x, y, d, p])
  | none := match match_neg y with
    | some y := do
      (zc, nc, d, p) ← prove_gcd_int x y,
      pure (zc, nc, d, `(int_gcd_helper_neg_right).mk_app [x, y, d, p])
    | none := do
      (zc, nc, nx, px) ← prove_nat_uncast zc nc x,
      (zc, nc, ny, py) ← prove_nat_uncast zc nc y,
      (nc, d, p) ← prove_gcd_nat nc nx ny,
      pure (zc, nc, d, `(int_gcd_helper).mk_app [x, y, nx, ny, d, px, py, p])
    end
  end

/-- Evaluates the `int.lcm` function. -/
meta def prove_lcm_int (zc nc : instance_cache) : expr → expr →
  tactic (instance_cache × instance_cache × expr × expr)
| x y := match match_neg x with
  | some x := do
    (zc, nc, d, p) ← prove_lcm_int x y,
    pure (zc, nc, d, `(int_lcm_helper_neg_left).mk_app [x, y, d, p])
  | none := match match_neg y with
    | some y := do
      (zc, nc, d, p) ← prove_lcm_int x y,
      pure (zc, nc, d, `(int_lcm_helper_neg_right).mk_app [x, y, d, p])
    | none := do
      (zc, nc, nx, px) ← prove_nat_uncast zc nc x,
      (zc, nc, ny, py) ← prove_nat_uncast zc nc y,
      (nc, d, p) ← prove_lcm_nat nc nx ny,
      pure (zc, nc, d, `(int_lcm_helper).mk_app [x, y, nx, ny, d, px, py, p])
    end
  end

/-- Evaluates the `nat.coprime` function. -/
meta def prove_coprime_nat (c : instance_cache) (ex ey : expr) :
  tactic (instance_cache × (expr ⊕ expr)) := do
  x ← ex.to_nat,
  y ← ey.to_nat,
  match x, y with
  | 1, _ := pure (c, sum.inl $ `(nat.coprime_one_left).mk_app [ey])
  | _, 1 := pure (c, sum.inl $ `(nat.coprime_one_right).mk_app [ex])
  | 0, 0 := pure (c, sum.inr `(nat.not_coprime_zero_zero))
  | 0, _ := do
    c ← mk_instance_cache `(ℕ),
    (c, p) ← prove_lt_nat c `(1) ey,
    pure (c, sum.inr $ `(nat_coprime_helper_zero_left).mk_app [ey, p])
  | _, 0 := do
    c ← mk_instance_cache `(ℕ),
    (c, p) ← prove_lt_nat c `(1) ex,
    pure (c, sum.inr $ `(nat_coprime_helper_zero_right).mk_app [ex, p])
  | _, _ := do
    c ← mk_instance_cache `(ℕ),
    let (d, a, b) := nat.xgcd_aux x 1 0 y 0 1,
    if d = 1 then do
      (c, ea) ← c.of_nat a.nat_abs,
      (c, eb) ← c.of_nat b.nat_abs,
      (c, etx, px) ← prove_mul_nat c ex ea,
      (c, ety, py) ← prove_mul_nat c ey eb,
      (c, p) ← if a ≥ 0 then prove_add_nat c ety `(1) etx else prove_add_nat c etx `(1) ety,
      let pf : expr := if a ≥ 0 then `(nat_coprime_helper_2) else `(nat_coprime_helper_1),
      pure (c, sum.inl $ pf.mk_app [ex, ey, ea, eb, etx, ety, px, py, p])
    else do
      (c, ed) ← c.of_nat d,
      (c, eu) ← c.of_nat (x / d),
      (c, ev) ← c.of_nat (y / d),
      (c, _, pu) ← prove_mul_nat c ed eu,
      (c, _, pv) ← prove_mul_nat c ed ev,
      (c, p) ← prove_lt_nat c `(1) ed,
      pure (c, sum.inr $ `(nat_not_coprime_helper).mk_app [ed, ex, ey, eu, ev, pu, pv, p])
  end

/-- Evaluates the `gcd`, `lcm`, and `coprime` functions. -/
@[norm_num] meta def eval_gcd : expr → tactic (expr × expr)
| `(nat.gcd %%ex %%ey) := do
    c ← mk_instance_cache `(ℕ),
    prod.snd <$> prove_gcd_nat c ex ey
| `(nat.lcm %%ex %%ey) := do
    c ← mk_instance_cache `(ℕ),
    prod.snd <$> prove_lcm_nat c ex ey
| `(nat.coprime %%ex %%ey) := do
    c ← mk_instance_cache `(ℕ),
    prove_coprime_nat c ex ey >>= sum.elim true_intro false_intro ∘ prod.snd
| `(int.gcd %%ex %%ey) := do
    zc ← mk_instance_cache `(ℤ),
    nc ← mk_instance_cache `(ℕ),
    (prod.snd ∘ prod.snd) <$> prove_gcd_int zc nc ex ey
| `(int.lcm %%ex %%ey) := do
    zc ← mk_instance_cache `(ℤ),
    nc ← mk_instance_cache `(ℕ),
    (prod.snd ∘ prod.snd) <$> prove_lcm_int zc nc ex ey
| _ := failed

end norm_num
end tactic

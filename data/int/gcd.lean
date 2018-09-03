/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl

Greatest common divisor (gcd) and least common multiple (lcm) for integers.

This sets up ℤ to be a GCD domain, and introduces rules about `int.gcd`, as well as `int.lcm`.
NOTE: If you add rules to this theory, check that the corresponding rules are available for
`gcd_domain`.
-/
import data.int.basic data.nat.prime algebra.gcd_domain

/- Extended Euclidean algorithm -/
namespace nat

def xgcd_aux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
| 0          s t r' s' t' := (r', s', t')
| r@(succ _) s t r' s' t' :=
  have r' % r < r, from mod_lt _ $ succ_pos _,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp] theorem xgcd_zero_left {s t r' s' t'} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by simp [xgcd_aux]

@[simp] theorem xgcd_aux_rec {r s t r' s' t'} (h : 0 < r) : xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
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
gcd.induction x y (by simp) (λ x y h IH s t s' t', by simp [h, IH]; rw ← gcd_rec)

theorem xgcd_aux_val (x y) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1]; cases xgcd_aux x 1 0 y 0 1; refl

theorem xgcd_val (x y) : xgcd x y = (gcd_a x y, gcd_b x y) :=
by unfold gcd_a gcd_b; cases xgcd x y; refl

section
parameters (a b : ℕ)

private def P : ℕ × ℤ × ℤ → Prop | (r, s, t) := (r : ℤ) = a * s + b * t

theorem xgcd_aux_P {r r'} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') → P (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by simp) $ λ x y h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, dsimp [P] at *,
  rw [int.mod_def], generalize : (y / x : ℤ) = k,
  rw [p, p'], simp [mul_add, mul_comm, mul_left_comm]
end

theorem gcd_eq_gcd_ab : (gcd a b : ℤ) = a * gcd_a a b + b * gcd_b a b :=
by have := @xgcd_aux_P a b a b 1 0 0 1 (by simp [P]) (by simp [P]);
   rwa [xgcd_aux_val, xgcd_val] at this
end

end nat

namespace int

theorem nat_abs_div (a b : ℤ) (H : b ∣ a) : nat_abs (a / b) = (nat_abs a) / (nat_abs b) :=
begin
  cases (nat.eq_zero_or_pos (nat_abs b)),
  rw eq_zero_of_nat_abs_eq_zero h,
  simp,
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
dvd.elim H (λl H1, by rw mul_assoc at H1; exact ⟨_, eq_of_mul_eq_mul_left k_non_zero H1⟩)

theorem dvd_of_mul_dvd_mul_right {i j k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) : i ∣ j :=
by rw [mul_comm i k, mul_comm j k] at H; exact dvd_of_mul_dvd_mul_left k_non_zero H

section normalization_domain

instance : normalization_domain ℤ :=
{ norm_unit      := λa:ℤ, if 0 ≤ a then 1 else -1,
  norm_unit_zero := if_pos (le_refl _),
  norm_unit_mul  := assume a b hna hnb,
  begin
    by_cases ha : 0 ≤ a; by_cases hb : 0 ≤ b; simp [ha, hb],
    exact if_pos (mul_nonneg ha hb),
    exact if_neg (assume h, hb $ nonneg_of_mul_nonneg_left h $ lt_of_le_of_ne ha hna.symm),
    exact if_neg (assume h, ha $ nonneg_of_mul_nonneg_right h $ lt_of_le_of_ne hb hnb.symm),
    exact if_pos (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (le_of_not_ge hb))
  end,
  norm_unit_coe_units := assume u, (units_eq_one_or u).elim
    (assume eq, eq.symm ▸ if_pos zero_le_one)
    (assume eq, eq.symm ▸ if_neg (not_le_of_gt $ show (-1:ℤ) < 0, by simp [@neg_lt ℤ _ 1 0])),
  .. (infer_instance : integral_domain ℤ) }

lemma norm_unit_of_nonneg {z : ℤ} (h : 0 ≤ z) : norm_unit z = 1 :=
by unfold norm_unit; exact if_pos h

lemma norm_unit_of_neg {z : ℤ} (h : z < 0) : norm_unit z = -1 :=
by unfold norm_unit; exact if_neg (not_le_of_gt h)

lemma norm_unit_nat_coe (n : ℕ) : norm_unit (n : ℤ) = 1 :=
norm_unit_of_nonneg (coe_nat_le_coe_nat_of_le $ nat.zero_le n)

theorem coe_nat_abs_eq_mul_norm_unit {z : ℤ} : (z.nat_abs : ℤ) = z * norm_unit z :=
begin
  by_cases 0 ≤ z,
  { simp [nat_abs_of_nonneg h, norm_unit_of_nonneg h] },
  { simp [of_nat_nat_abs_of_nonpos (le_of_not_ge h), norm_unit_of_neg (lt_of_not_ge h)] }
end

end normalization_domain

/-- ℤ specific version of least common multiple. -/
def lcm (i j : ℤ) : ℕ := nat.lcm (nat_abs i) (nat_abs j)

theorem lcm_def (i j : ℤ) : lcm i j = nat.lcm (nat_abs i) (nat_abs j) := rfl

section gcd_domain

theorem gcd_dvd_left (i j : ℤ) : (gcd i j : ℤ) ∣ i :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_left _ _

theorem gcd_dvd_right (i j : ℤ) : (gcd i j : ℤ) ∣ j :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_right _ _

theorem dvd_gcd {i j k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ gcd i j :=
nat_abs_dvd.1 $ coe_nat_dvd.2 $ nat.dvd_gcd (nat_abs_dvd_abs_iff.2 h1) (nat_abs_dvd_abs_iff.2 h2)

theorem gcd_mul_lcm (i j : ℤ) : gcd i j * lcm i j = nat_abs (i * j) :=
by rw [int.gcd, int.lcm, nat.gcd_mul_lcm, nat_abs_mul]

instance : gcd_domain ℤ :=
{ gcd            := λa b, int.gcd a b,
  lcm            := λa b, int.lcm a b,
  gcd_dvd_left   := assume a b, int.gcd_dvd_left _ _,
  gcd_dvd_right  := assume a b, int.gcd_dvd_right _ _,
  dvd_gcd        := assume a b c, dvd_gcd,
  norm_unit_gcd  := assume a b, norm_unit_nat_coe _,
  gcd_mul_lcm    := by intros; rw [← int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_mul_norm_unit],
  lcm_zero_left  := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_left _,
  lcm_zero_right := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_right _,
  .. int.normalization_domain }

lemma coe_gcd (i j : ℤ) : ↑(int.gcd i j) = gcd_domain.gcd i j := rfl
lemma coe_lcm (i j : ℤ) : ↑(int.lcm i j) = gcd_domain.lcm i j := rfl

lemma nat_abs_gcd (i j : ℤ) : nat_abs (gcd_domain.gcd i j) = int.gcd i j := rfl
lemma nat_abs_lcm (i j : ℤ) : nat_abs (gcd_domain.lcm i j) = int.lcm i j := rfl

end gcd_domain

theorem gcd_comm (i j : ℤ) : gcd i j = gcd j i := nat.gcd_comm _ _

theorem gcd_assoc (i j k : ℤ) : gcd (gcd i j) k = gcd i (gcd j k) := nat.gcd_assoc _ _ _

@[simp] theorem gcd_self (i : ℤ) : gcd i i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_left (i : ℤ) : gcd 0 i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_right (i : ℤ) : gcd i 0 = nat_abs i := by simp [gcd]

@[simp] theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 := nat.gcd_one_left _

@[simp] theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 := nat.gcd_one_right _

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = nat_abs i * gcd j k :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_gcd, coe_nat_abs_eq_mul_norm_unit]

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * nat_abs j :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_gcd, coe_nat_abs_eq_mul_norm_unit]

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : gcd i j > 0 :=
nat.gcd_pos_of_pos_left (nat_abs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : gcd i j > 0 :=
nat.gcd_pos_of_pos_right (nat_abs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem gcd_eq_zero_iff {i j : ℤ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
by rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_zero, coe_gcd, gcd_eq_zero_iff]

theorem gcd_div {i j k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) :
  gcd (i / k) (j / k) = gcd i j / nat_abs k :=
by rw [gcd, nat_abs_div i k H1, nat_abs_div j k H2];
exact nat.gcd_div (nat_abs_dvd_abs_iff.mpr H1) (nat_abs_dvd_abs_iff.mpr H2)

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
int.coe_nat_dvd.1 $ dvd_gcd (dvd.trans (gcd_dvd_left i j) H) (gcd_dvd_right i j)

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
int.coe_nat_dvd.1 $ dvd_gcd (gcd_dvd_left j i) (dvd.trans (gcd_dvd_right j i) H)

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

/- lcm -/

theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, lcm_comm]

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, lcm_assoc]

@[simp] theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm]

@[simp] theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm]

@[simp] theorem lcm_one_left (i : ℤ) : lcm 1 i = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_mul_norm_unit]

@[simp] theorem lcm_one_right (i : ℤ) : lcm i 1 = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_mul_norm_unit]

@[simp] theorem lcm_self (i : ℤ) : lcm i i = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_mul_norm_unit]

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j :=
by rw [coe_lcm]; exact dvd_lcm_left _ _

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j :=
by rw [coe_lcm]; exact dvd_lcm_right _ _

theorem lcm_dvd {i j k : ℤ}  : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k :=
by rw [coe_lcm]; exact lcm_dvd

end int

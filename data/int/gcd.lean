/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy

Lemmas and extended definitions and properties of gcd and lcm for integers.
-/

import data.int.basic data.nat.basic data.nat.gcd

namespace int

/- gcd -/

@[simp] theorem gcd_self (i : ℤ) : gcd i i = nat_abs i :=
by cases i; simp [gcd, mod_self]

@[simp] theorem gcd_zero_left (i : ℤ) : gcd 0 i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_right (i : ℤ) : gcd i 0 = nat_abs i :=
by cases i; simp [gcd]

theorem gcd_dvd_left (i j : ℤ) : (gcd i j : ℤ) ∣ i := 
dvd_nat_abs.mp (coe_nat_dvd.mpr (nat.gcd_dvd_left (nat_abs i) (nat_abs j)))

theorem gcd_dvd_right (i j : ℤ) : (gcd i j : ℤ) ∣ j :=
dvd_nat_abs.mp (coe_nat_dvd.mpr (nat.gcd_dvd_right (nat_abs i) (nat_abs j)))

theorem gcd_dvd (i j : ℤ) : ((gcd i j : ℤ) ∣ i) ∧ ((gcd i j : ℤ) ∣ j) := 
⟨gcd_dvd_left i j, gcd_dvd_right i j⟩

theorem dvd_gcd {i j k : ℤ} : k ∣ i → k ∣ j → k ∣ gcd i j :=
by intros H1 H2; 
exact nat_abs_dvd.mp (coe_nat_dvd.mpr (nat.dvd_gcd (nat_abs_dvd_abs_iff.mpr H1) 
                                                   (nat_abs_dvd_abs_iff.mpr H2)))

theorem gcd_comm (i j : ℤ) : gcd i j = gcd j i := 
nat.gcd_comm (nat_abs i) (nat_abs j)

theorem gcd_assoc (i j k : ℤ) : gcd (gcd i j) k = gcd i (gcd j k) :=
nat.gcd_assoc (nat_abs i) (nat_abs j) (nat_abs k)

@[simp] theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 := nat.gcd_one_left _

@[simp] theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 :=
eq.trans (gcd_comm i 1) $ gcd_one_left i

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = nat_abs i * gcd j k :=
by rw [gcd, nat_abs_mul, nat_abs_mul]; 
exact nat.gcd_mul_left (nat_abs i) (nat_abs j) (nat_abs k)

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * nat_abs j := 
by rw [gcd, nat_abs_mul, nat_abs_mul]; 
exact nat.gcd_mul_right (nat_abs i) (nat_abs j) (nat_abs k)

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : gcd i j > 0 :=
nat.gcd_pos_of_pos_left (nat_abs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : gcd i j > 0 :=
nat.gcd_pos_of_pos_right (nat_abs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem eq_zero_of_gcd_eq_zero_left {i j : ℤ} (H : gcd i j = 0) : i = 0 :=
eq_zero_of_nat_abs_eq_zero (nat.eq_zero_of_gcd_eq_zero_left H)

theorem eq_zero_of_gcd_eq_zero_right {i j : ℤ} (H : gcd i j = 0) : j = 0 :=
eq_zero_of_nat_abs_eq_zero (nat.eq_zero_of_gcd_eq_zero_right H)

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
                 (by unfold gcd; exact nat.dvd_gcd (dvd_refl _) (nat_abs_dvd_abs H))

theorem gcd_eq_right {i j : ℤ} (H : j ∣ i) : gcd i j = nat_abs j :=
by rw [gcd_comm, gcd_eq_left H]

/- lcm -/

def lcm (i j : ℤ) : ℕ := nat_abs(i * j) / (gcd i j)

theorem lcm_def (i j : ℤ) : lcm i j = nat.lcm (nat_abs i) (nat_abs j) :=
by rw [lcm, nat.lcm, gcd, nat_abs_mul]

theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i :=
by delta lcm; rw [mul_comm, gcd_comm]

theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 :=
by rw [lcm, zero_mul, gcd_zero_left]; by simp

theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 := lcm_comm 0 i ▸ lcm_zero_left i

theorem lcm_one_left (i : ℤ) : lcm 1 i = nat_abs i :=
by rw [lcm, one_mul, gcd_one_left, nat.div_one]

theorem lcm_one_right (i : ℤ) : lcm i 1 = nat_abs i := 
by unfold lcm; simp

theorem lcm_self (i : ℤ) : lcm i i = nat_abs i :=
by rw [lcm, gcd_self, nat_abs_mul, nat.mul_div_assoc, mul_comm, nat.div_mul_cancel]; 
simp; simp

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j :=
nat_abs_dvd.mp (coe_nat_dvd.mpr (eq.subst (eq.symm (lcm_def i j)) 
                                          (nat.dvd_lcm_left (nat_abs i) (nat_abs j))))

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j :=
lcm_comm j i ▸ dvd_lcm_left j i

theorem gcd_mul_lcm (i j : ℤ) : gcd i j * lcm i j = nat_abs (i * j) :=
begin
  rw [lcm, mul_comm, nat.div_mul_cancel],
  exact eq.subst (eq.symm (nat_abs_mul i j)) 
                 (dvd_mul_of_dvd_left (coe_nat_dvd.mp (dvd_nat_abs.mpr (gcd_dvd_left i j))) _),
end

theorem lcm_dvd {i j k : ℤ} (H1 : i ∣ k) (H2 : j ∣ k) : (lcm i j : ℤ) ∣ k :=
dvd_nat_abs.mp (coe_nat_dvd.mpr (eq.subst (eq.symm (lcm_def i j)) 
                                          (nat.lcm_dvd (nat_abs_dvd_abs_iff.mpr H1)
                                                       (nat_abs_dvd_abs_iff.mpr H2))))

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) :=
by rw [lcm_def, lcm_def, lcm_def, lcm_def];
exact nat.lcm_assoc (nat_abs i) (nat_abs j) (nat_abs k)

/- lemmas -/

theorem dvd_of_mul_dvd_mul_left {i j k : ℤ} (k_non_zero : k ≠ 0) (H : k * i ∣ k * j) : i ∣ j :=
dvd.elim H (λl H1, by rw mul_assoc at H1; exact ⟨_, eq_of_mul_eq_mul_left k_non_zero H1⟩)

theorem dvd_of_mul_dvd_mul_right {i j k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) : i ∣ j :=
by rw [mul_comm i k, mul_comm j k] at H; exact dvd_of_mul_dvd_mul_left k_non_zero H


end int

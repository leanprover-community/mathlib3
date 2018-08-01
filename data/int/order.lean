/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
import data.int.basic

namespace int

lemma of_nat_le_of_nat_of_le {n m : ℕ} (h : n ≤ m) : of_nat n ≤ of_nat m :=
coe_nat_le_coe_nat_of_le h

lemma le_of_of_nat_le_of_nat {n m : ℕ} (h : of_nat n ≤ of_nat m) : n ≤ m :=
let ⟨i, (hi : of_nat n + of_nat i = of_nat m)⟩ := le.dest h in
have i + n = m, by apply int.of_nat_inj; rwa [add_comm, of_nat_add],
this ▸ nat.le_add_left _ _

end int

/-
/- more facts specific to int -/

theorem coe_nat_nonneg (n : ℕ) : 0 ≤ ↑n := trivial

theorem coe_nat_pos {n : ℕ} (Hpos : #nat n > 0) : ↑n > 0 :=
coe_nat_lt_coe_nat_of_lt Hpos

theorem coe_nat_succ_pos (n : nat) : ↑(nat.succ n) > 0 :=
coe_nat_pos !nat.succ_pos

theorem exists_eq_coe_nat {a : ℤ} (H : 0 ≤ a) : ∃n : ℕ, a = ↑n :=
obtain (n : ℕ) (H1 : 0 + ↑n = a), from le.dest H,
exists.intro n (!zero_add ▸ (H1⁻¹))

theorem exists_eq_neg_coe_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -(↑n) :=
have -a ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos H,
obtain (n : ℕ) (Hn : -a = ↑n), from exists_eq_coe_nat this,
exists.intro n (eq_neg_of_eq_neg (Hn⁻¹))

theorem coe_nat_nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : ↑(nat_abs a) = a :=
obtain (n : ℕ) (Hn : a = ↑n), from exists_eq_coe_nat H,
Hn⁻¹ ▸ congr_arg coe_nat (nat_abs_↑n)

theorem coe_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : ↑(nat_abs a) = -a :=
have -a ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos H,
calc
  coe_nat (nat_abs a) = coe_nat (nat_abs (-a)) : nat_abs_neg
                 ... = -a                    : coe_nat_nat_abs_of_nonneg this

theorem coe_nat_nat_abs (b : ℤ) : nat_abs b = abs b :=
or.elim (le.total 0 b)
  (assume H : b ≥ 0, coe_nat_nat_abs_of_nonneg H ⬝ (abs_of_nonneg H)⁻¹)
  (assume H : b ≤ 0, coe_nat_nat_abs_of_nonpos H ⬝ (abs_of_nonpos H)⁻¹)

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
abs.by_cases rfl !nat_abs_neg

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
obtain (n : nat) (H1 : a + 1 + n = b), from le.dest H,
have a + succ n = b, by rw [← H1, add.assoc, add.comm 1],
lt.intro this

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
obtain (n : nat) (H1 : a + succ n = b), from lt.elim H,
have a + 1 + n = b, by rw [← H1, add.assoc, add.comm 1],
le.intro this

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
lt_add_of_le_of_pos H trivial

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
have H1 : a + 1 ≤ b + 1, from add_one_le_of_lt H,
le_of_add_le_add_right H1

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
lt_of_add_one_le (begin rw sub_add_cancel, exact H end)

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
!sub_add_cancel ▸ add_one_le_of_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
le_of_lt_add_one begin rw sub_add_cancel, exact H end

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
!sub_add_cancel ▸ (lt_add_one_of_le H)

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 :=
sign_of_pos (coe_nat_pos !nat.succ_pos)

theorem exists_eq_neg_succ_coe_nat {a : ℤ} : a < 0 → ∃m : ℕ, a = -[1+m] :=
int.cases_on a
  (assume (m : nat) H, absurd (coe_nat_nonneg m : 0 ≤ m) (not_le_of_gt H))
  (assume (m : nat) H, exists.intro m rfl)

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : a ≥ 0) (H' : a * b = 1) : a = 1 :=
have a * b > 0, by rw H'; apply trivial,
have b > 0, from pos_of_mul_pos_left this H,
have a > 0, from pos_of_mul_pos_right `a * b > 0` (le_of_lt `b > 0`),
or.elim (le_or_gt a 1)
  (assume : a ≤ 1,
    show a = 1, from le.antisymm this (add_one_le_of_lt `a > 0`))
  (assume : a > 1,
    have a * b ≥ 2 * 1,
      from mul_le_mul (add_one_le_of_lt `a > 1`) (add_one_le_of_lt `b > 0`) trivial H,
    have false, by rw H' at this; exact this,
    false.elim this)

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : b ≥ 0) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (!mul.comm ▸ H')

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
eq_of_mul_eq_mul_right Hpos (H ⬝ (one_mul a)⁻¹)

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
eq_one_of_mul_eq_self_left Hpos (!mul.comm ▸ H)

theorem eq_one_of_dvd_one {a : ℤ} (H : a ≥ 0) (H' : a ∣ 1) : a = 1 :=
dvd.elim H'
  (assume b,
    assume : 1 = a * b,
    eq_one_of_mul_eq_one_right H this⁻¹)

theorem exists_least_of_bdd {P : ℤ → Prop} [HP : decidable_pred P]
    (Hbdd : ∃ b : ℤ, ∀ z : ℤ, z ≤ b → ¬ P z)
        (Hinh : ∃ z : ℤ, P z) : ∃ lb : ℤ, P lb ∧ (∀ z : ℤ, z < lb → ¬ P z) :=
  begin
    cases Hbdd with [b, Hb],
    cases Hinh with [elt, Helt],
    existsi b + coe_nat (least (λ n, P (b + ↑n)) (nat.succ (nat_abs (elt - b)))),
    have Heltb : elt > b, begin
      apply lt_of_not_ge,
      intro Hge,
      apply (Hb _ Hge) Helt
    end,
    have H' : P (b + coe_nat (nat_abs (elt - b))), begin
      rw [coe_nat_nat_abs_of_nonneg (int.le_of_lt (iff.mpr !sub_pos_iff_lt Heltb)),
              add.comm, sub_add_cancel],
      apply Helt
    end,
    apply and.intro,
    apply least_of_lt _ !lt_succ_self H',
    intros z Hz,
    cases em (z ≤ b) with [Hzb, Hzb],
    apply Hb _ Hzb,
    let Hzb' := lt_of_not_ge Hzb,
    let Hpos := iff.mpr !sub_pos_iff_lt Hzb',
    have Hzbk : z = b + coe_nat (nat_abs (z - b)),
      by rw [coe_nat_nat_abs_of_nonneg (int.le_of_lt Hpos), int.add_comm, sub_add_cancel],
    have Hk : nat_abs (z - b) < least (λ n, P (b + ↑n)) (nat.succ (nat_abs (elt - b))), begin
     have Hz' := iff.mp !lt_add_iff_sub_lt_left Hz,
     rw [←coe_nat_nat_abs_of_nonneg (int.le_of_lt Hpos) at Hz'],
     apply lt_of_coe_nat_lt_coe_nat Hz'
    end,
    let Hk' := not_le_of_gt Hk,
    rw Hzbk,
    apply λ p, mt (ge_least_of_lt _ p) Hk',
    apply nat.lt_trans Hk,
    apply least_lt _ !lt_succ_self H'
  end

theorem exists_greatest_of_bdd {P : ℤ → Prop} [HP : decidable_pred P]
    (Hbdd : ∃ b : ℤ, ∀ z : ℤ, z ≥ b → ¬ P z)
        (Hinh : ∃ z : ℤ, P z) : ∃ ub : ℤ, P ub ∧ (∀ z : ℤ, z > ub → ¬ P z) :=
  begin
    cases Hbdd with [b, Hb],
    cases Hinh with [elt, Helt],
    existsi b - coe_nat (least (λ n, P (b - ↑n)) (nat.succ (nat_abs (b - elt)))),
    have Heltb : elt < b, begin
      apply lt_of_not_ge,
      intro Hge,
      apply (Hb _ Hge) Helt
    end,
    have H' : P (b - coe_nat (nat_abs (b - elt))), begin
      rw [coe_nat_nat_abs_of_nonneg (int.le_of_lt (iff.mpr !sub_pos_iff_lt Heltb)),
              sub_sub_self],
      apply Helt
    end,
    apply and.intro,
    apply least_of_lt _ !lt_succ_self H',
    intros z Hz,
    cases em (z ≥ b) with [Hzb, Hzb],
    apply Hb _ Hzb,
    let Hzb' := lt_of_not_ge Hzb,
    let Hpos := iff.mpr !sub_pos_iff_lt Hzb',
    have Hzbk : z = b - coe_nat (nat_abs (b - z)),
      by rw [coe_nat_nat_abs_of_nonneg (int.le_of_lt Hpos), sub_sub_self],
    have Hk : nat_abs (b - z) < least (λ n, P (b - ↑n)) (nat.succ (nat_abs (b - elt))), begin
      have Hz' := iff.mp !lt_add_iff_sub_lt_left (iff.mpr !lt_add_iff_sub_lt_right Hz),
      rw [←coe_nat_nat_abs_of_nonneg (int.le_of_lt Hpos) at Hz'],
      apply lt_of_coe_nat_lt_coe_nat Hz'
    end,
    let Hk' := not_le_of_gt Hk,
    rw Hzbk,
    apply λ p, mt (ge_least_of_lt _ p) Hk',
    apply nat.lt_trans Hk,
    apply least_lt _ !lt_succ_self H'
  end

end int
-/

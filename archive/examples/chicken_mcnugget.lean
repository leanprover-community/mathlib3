/-
Copyright (c) 2021 Alex Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zhao
-/
import tactic.suggest
import tactic.linarith.frontend
import data.rat.basic
import data.nat.prime
import data.int.gcd

/-!
# Chicken McNugget Theorem

In this file we prove the Chicken McNugget Theorem.

## Theorem Statement:
The Chicken McNugget Theorem states,
for two relatively prime integers larger than 1,
the largest integer not writeable as a sum of multiples of these two
is m * n - m - n.

## Implementation Notes

This proof uses Bezout's greatest common divisor theorem
to create a construction, and uses inequalities to show
m * n - m - n cannot be written as a sum of multiples,
upper bounding the largest nonconstructible number.

## Tags

chicken nugget, frobenius coin
-/

open nat

/-- Distributivity of coercion from N to Z over subtraction, using casework. -/
lemma coe_sub_ge (m n : ℕ):
  (m : ℤ)-(n : ℤ) ≤ (((m-n) : ℕ):ℤ) :=
by by_cases m ≥ n; [norm_cast, linarith]

/-- This lemma shows there is no solution for the maximal value over positive integers. -/
lemma chicken_mcnugget_upper_bound_ints (a b m n : ℤ) (mpos: m>1) (npos: n>1) (cop: m.gcd n = 1)
  (anonneg: a≥0) (bnonneg: b≥0):
    ¬ a*m+b*n=m*n-m-n :=
begin
  intro h,

  --algebra
  have id1 := mul_sub m n 1,
  rw mul_one at id1,
  rw [← id1,(mul_comm a m)] at h,
  have id2 := int.add_zero (n-1),
  rw [← add_left_neg (a)] at id2,
  rw [← id2,← add_assoc,mul_add,add_comm (m * (n - 1 + -a)) (m*a),add_sub_assoc] at h,
  have h2 := add_left_cancel h,
  rw [← add_zero (b*n),← add_left_neg n,sub_eq_add_neg _ n,
    ← add_assoc,add_comm (b*n) (-n),add_comm _ (-n),add_assoc] at h2,
  have h3 := add_left_cancel h2,
  have h : b*n+n=n*(b+1),
  rw mul_add,
  simp,
  exact mul_comm b n,
  rw [h,← sub_eq_add_neg (n-1) a] at h3,
  --ineqs
  have bp1bound := int.add_lt_add_of_le_of_lt bnonneg zero_lt_one,
  rw zero_add at bp1bound,
  have LHSbound := int.mul_lt_mul_of_pos_left bp1bound (lt_trans int.zero_lt_one npos),
  rw [mul_zero,h3] at LHSbound,
  --divide by pos amount
  by_cases h : n-1-a<=0,
  {
    have contra := int.mul_le_mul_of_nonpos_right (int.le_of_lt (lt_trans int.zero_lt_one mpos)) h,
    rw zero_mul at contra,
    exact not_lt_of_le contra LHSbound,
  },
  push_neg at h,
  have div := dvd_mul_right n (b+1),
  rw h3 at div,
  have lcmdivision := int.lcm_dvd (dvd_mul_right m (n-1-a)) div,
  have lcmprod := int.gcd_mul_lcm m n,
  rw [cop,one_mul] at lcmprod,
  have mnpos := int.mul_pos (lt_trans int.zero_lt_one mpos) (lt_trans int.zero_lt_one npos),
  rw [lcmprod, ← int.eq_nat_abs_of_zero_le (le_of_lt mnpos)] at lcmdivision,
  have contra := int.le_of_dvd h (int.dvd_of_mul_dvd_mul_left
    (ne_of_gt (lt_trans int.zero_lt_one mpos)) lcmdivision),
  have mainbound2 := int.lt_add_one_of_le (int.sub_le_self (n-1) anonneg),
  rw sub_add_cancel at mainbound2,
  exact not_lt_of_le contra mainbound2,
end

/-- No solution for the maximal value over the natural numbers, cleanly -/
lemma chicken_mcnugget_upper_bound (m n : ℕ) (cop : m.gcd n = 1) (mlb: m>1) (nlb: n>1):
  ¬ ∃ (a b : ℕ), a*m+b*n=m*n-m-n :=
begin
  intros h,
  cases h with a h,
  cases h with b h,
  have int_h : (((a * m + b * n):ℕ):ℤ) = (((m * n - m - n):ℕ):ℤ),
  rw h,
  rw [int.coe_nat_add,int.coe_nat_sub,int.coe_nat_sub] at int_h,
  repeat {rw int.coe_nat_mul at int_h},
  have intcop : (m:ℤ).gcd (n:ℤ)=1,
  rw int.coe_nat_gcd m n,
  exact cop,
  exact chicken_mcnugget_upper_bound_ints (a:ℤ) (b:ℤ) (m:ℤ) (n:ℤ)
    (int.coe_nat_lt.2 mlb) (int.coe_nat_lt.2 nlb)
      intcop (int.coe_nat_nonneg a) (int.coe_nat_nonneg b) int_h,
  have close := nat.mul_le_mul_left m (le_of_lt nlb),
  rw mul_one at close,
  exact close,
  have alb2 := nat.mul_lt_mul_of_pos_right mlb (nat.sub_pos_of_lt nlb),
  rw [(nat.mul_sub_left_distrib m n 1), mul_one, one_mul] at alb2,
  have closing := nat.succ_le_of_lt alb2,
  rw [succ_eq_add_one, (nat.sub_add_cancel (le_of_lt nlb))] at closing,
  exact closing,
end

/-- Constructs solutions for values greater than the maximal value over the positive integers. -/
lemma chicken_mcnugget_construction_ints (m n: ℤ) (mlb: m>1) (nlb: n>1) (cop: m.gcd n=1):
  ∀ (k : ℤ), k>m*n-m-n → ∃ (a b : ℤ), a*m+b*n=k ∧ a>=0 ∧ b>=0 :=
begin
  --intros
  intro k,
  intro kbound,

  --manipulation
  have bezout := int.gcd_eq_gcd_ab m n,
  rw [cop,int.coe_nat_one] at bezout,
  have bezout2 : k*1 = k*(m * m.gcd_a n + n * m.gcd_b n),
  rw bezout,
  rw [mul_one,mul_add] at bezout2,
  repeat {rw [← mul_assoc] at bezout2},
  set p := (k*m.gcd_a n)%n with hp,
  set q := ((k*m.gcd_a n)/n*m)+(k*m.gcd_b n) with hq,
  refine ⟨p,q,_⟩,
  have part1 : p * m + q * n = k,
  rw [hq,hp],
  have claim : n * (k * m.gcd_a n / n) + k * m.gcd_a n % n-n * (k * m.gcd_a n / n)
    =k * m.gcd_a n-n * (k * m.gcd_a n / n),
  rw (int.div_add_mod (k*m.gcd_a n) n),

  rw [add_comm, add_sub_cancel] at claim,
  rw [claim,int.sub_mul,add_mul,← add_assoc,mul_comm n _,mul_assoc _ n m, mul_comm n m,
    ← mul_assoc _ m n, sub_add_cancel,mul_assoc k _ m,mul_assoc k _ n,mul_comm _ m,mul_comm _ n,
    ← mul_assoc,← mul_assoc,← bezout2],

  have pnonneg := int.mod_nonneg (k * m.gcd_a n) (ne_of_gt (lt_trans int.zero_lt_one nlb)),
  rw [← hp] at pnonneg,
  split,
  exact part1,
  split,
  exact pnonneg,
  by_contradiction,
  push_neg at h,
  rw [← part1] at kbound,
  have pbound := int.mod_lt_of_pos (k * m.gcd_a n) (lt_trans int.zero_lt_one nlb),
  rw [← hp] at pbound,
  rw [← sub_add_cancel n 1] at pbound,
  have pbound2 := int.lt_add_one_iff.1 pbound,
  have pbound3 := int.mul_le_mul_of_nonneg_right pbound2 (le_of_lt (lt_trans int.zero_lt_one mlb)),
  have qbound := int.sub_lt_sub_of_lt_of_le kbound pbound3,
  rw [add_comm,add_sub_cancel,sub_mul,← sub_add,one_mul] at qbound,
  have qbound3 := int.le_sub_right_of_add_le ((int.lt_iff_add_one_le q 0).1 h),
  have qbound4 := int.mul_le_mul_of_nonneg_right qbound3 (le_of_lt (lt_trans int.zero_lt_one nlb)),
  rw [sub_mul,zero_mul,one_mul] at qbound4,
  have qbound5 := int.add_le_add_right qbound4 n,
  rw sub_add_cancel at qbound5,
  repeat {rw sub_sub at qbound},
  rw [add_comm n _, ← add_assoc, add_comm m _, add_assoc, add_comm m n, ← add_assoc, ← sub_sub,
    ← sub_sub, mul_comm n m, sub_add_cancel] at qbound,
  have contra := int.add_lt_add_right qbound n,
  rw sub_add_cancel at contra,
  rw (int.sub_self (m*n)) at contra,
  exact not_lt_of_le qbound5 contra,
end

/-- Constructs solutions to values greater than the maximal value over the natural numbers. -/
lemma chicken_mcnugget_construction (m n: ℕ) (mpos: m>1) (npos: n>1) (cop: m.gcd n=1):
  ∀ (k:ℕ), k>m*n-m-n → ∃ (a b : ℕ), a*m+b*n=k :=
begin
  intros k kbound,
  have intcop : (m:ℤ).gcd(n:ℤ) = 1,
  rw int.coe_nat_gcd,
  exact cop,

  have intkbound : (k:ℤ) > (m:ℤ) * (n:ℤ) - (m:ℤ) - (n:ℤ),
  have kbound4 := lt_of_le_of_lt (int.sub_le_sub_right (coe_sub_ge (m*n) m) n)
    (lt_of_le_of_lt (coe_sub_ge (m*n-m) n) (int.coe_nat_lt.2 kbound)),
  rw int.coe_nat_mul at kbound4,
  exact kbound4,

  -- "importing" the result from the ints
  have thing := chicken_mcnugget_construction_ints (m:ℤ) (n:ℤ)
    (int.coe_nat_lt.2 mpos) (int.coe_nat_lt.2 npos) intcop (k:ℤ) intkbound,
  rcases thing with ⟨a, b, relation, bounds⟩,
  cases bounds with anonneg bnonneg,

  refine ⟨int.nat_abs a, int.nat_abs b, _⟩,
  have nat_relation : int.nat_abs (a*(m:ℤ)+b*(n:ℤ)) = int.nat_abs(k:ℤ),
  rw relation,
  rw int.nat_abs_of_nat at nat_relation,
  have left_nonneg := int.mul_le_mul anonneg (int.coe_nat_nonneg m) (le_of_eq (refl 0)) anonneg,
  rw zero_mul at left_nonneg,
  have right_nonneg := int.mul_le_mul bnonneg (int.coe_nat_nonneg n) (le_of_eq (refl 0)) bnonneg,
  rw mul_zero at right_nonneg,
  rw (int.nat_abs_add_nonneg left_nonneg right_nonneg) at nat_relation,
  repeat {rw int.nat_abs_mul at nat_relation},
  have thingm := int.nat_abs_of_nat_core m,
  have thingn := int.nat_abs_of_nat_core n,
  rw int.of_nat_eq_coe at thingm,
  rw int.of_nat_eq_coe at thingn,
  rw [thingm, thingn] at nat_relation,
  exact nat_relation,
end

/-- This theorem combines both sublemmas in a single claim. -/
theorem chicken_mcnugget (m n: ℕ) (mlb: m>1) (nlb: n>1) (cop: m.gcd n=1):
  (¬ ∃ (a b : ℕ), a*m+b*n=m*n-m-n) ∧ ∀ (k:ℕ), k>m*n-m-n → ∃ (a b : ℕ), a*m+b*n=k :=
begin
  split,
  exact (chicken_mcnugget_upper_bound m n cop mlb nlb),
  exact (chicken_mcnugget_construction m n mlb nlb cop),
end

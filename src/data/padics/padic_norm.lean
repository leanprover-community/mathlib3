/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic valuation on ℤ and ℚ, and the p-adic norm on ℚ
-/

import data.rat data.int.gcd algebra.field_power
import tactic.wlog tactic.ring

universe u
open nat

attribute [class] nat.prime

private lemma exi_div (p : ℕ) (n : ℤ) : ∃ k : ℕ, k ≤ n.nat_abs ∧ ↑(p ^ k) ∣ n :=
⟨0, nat.zero_le _, by simp⟩

private lemma bound {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) :
  ∀ k : ℕ, k > n.nat_abs → ¬ (↑(p ^ k) ∣ n) :=
assume k (hkn : k > n.nat_abs),
have n.nat_abs < p^k, from lt.trans (lt_pow_self hp _) (pow_lt_pow_of_lt_right hp hkn),
assume hdvd : ↑(p ^ k) ∣ n,
have hdvd' : (p ^ k) ∣ n.nat_abs, from int.dvd_nat_abs_of_of_nat_dvd hdvd,
let hle := le_of_dvd (int.nat_abs_pos_of_ne_zero hn) hdvd' in
not_le_of_gt this hle

def padic_val (p : ℕ) (n : ℤ) : ℕ :=
if hn : n = 0 then 0
else if hp : p > 1 then nat.find_greatest (λ k, ↑(p ^ k) ∣ n) n.nat_abs
else 0

namespace padic_val

lemma spec {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) : ↑(p ^ padic_val p n) ∣ n :=
let ha := nat.find_greatest_spec (exi_div p n) in
by simpa [padic_val, hp, hn] using ha

lemma is_greatest {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) (m : ℕ) (hm : m > padic_val p n) :
  ¬ ↑(p ^ m) ∣ n :=
let ha := nat.find_greatest_is_greatest (exi_div p n) in
if hmb : m ≤ n.nat_abs then
  have hfg : nat.find_greatest (λ (m : ℕ), ↑(p ^ m) ∣ n) (int.nat_abs n) < m,
    by simpa [padic_val, hn, hp] using hm,
  ha _ ⟨hfg, hmb⟩
else bound hp hn _ $ lt_of_not_ge hmb

lemma unique {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) {k : ℕ} (hk : ↑(p^k) ∣ n)
  (hall : ∀ m : ℕ, m > k → ¬ ↑(p^m) ∣ n) : k = padic_val p n :=
have hle : k ≤ padic_val p n, from le_of_not_gt $ λ h, is_greatest hp hn _ h hk,
have hge : k ≥ padic_val p n, from le_of_not_gt $ λ h, hall _ h (spec hp hn),
le_antisymm hle hge

@[simp] protected lemma neg {p : ℕ} (hp : p > 1) (n : ℤ) : padic_val p (-n) = padic_val p n :=
if hn : n = 0 then by simp [hn] else
have hnn : -n ≠ 0, by simp [hn],
unique hp hn
  (have ↑(p ^ padic_val p (-n)) ∣ (-n), from spec hp hnn, dvd_of_dvd_neg this)
  (assume m hm (hdiv : (↑(p^m) ∣ n)),
   have ↑(p^m) ∣ (-n), from dvd_neg_of_dvd hdiv,
   is_greatest hp  hnn _ hm this)

lemma le_padic_val_of_pow_dvd {p k : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) (h : ↑(p^k) ∣ n) :
  k ≤ padic_val p n :=
le_of_not_gt $
  assume : k > padic_val p n,
  is_greatest hp hn _ this h

lemma pow_dvd_of_le_padic_val {p k : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) (h : k ≤ padic_val p n) :
  ↑(p^k) ∣ n :=
int.pow_dvd_of_le_of_pow_dvd h (spec hp hn)

lemma pow_dvd_iff_le_padic_val {p k : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) :
  ↑(p^k) ∣ n ↔ k ≤ padic_val p n :=
⟨le_padic_val_of_pow_dvd hp hn, pow_dvd_of_le_padic_val hp hn⟩

section
variables {p : ℕ} (hp : p > 1)

@[simp] protected lemma zero : padic_val p 0 = 0 := by simp [padic_val]

include hp
@[simp] protected lemma one : padic_val p 1 = 0 :=
begin
  symmetry,
  apply unique,
  repeat { norm_num },
  { assumption },
  { intros k hk,
    have h1k : 1 ^ k < p ^ k, from pow_lt_pow_of_lt_left hp hk,
    rw nat.one_pow at h1k,
    intro hdvd,
    apply not_le_of_gt h1k,
    apply le_of_dvd zero_lt_one,
    apply int.coe_nat_dvd.1,
    simpa }
end

@[simp] lemma padic_val_self : padic_val p p = 1 :=
have h : p ≠ 0, by intro h'; subst h'; exact absurd hp dec_trivial,
begin
  symmetry, apply unique; simp *,
  intros k hk hdvd,
  apply not_pos_pow_dvd hp hk,
  rw ← int.coe_nat_dvd, simpa
end

end

lemma padic_val_eq_zero_of_not_dvd {p : ℕ} {n : ℤ} (hnd : ¬ ↑p ∣ n) : padic_val p n = 0 :=
if h : n = 0 then by simp [h] else
if hp : p > 1 then
  eq.symm $ padic_val.unique hp h (by simp) $ λ m hm hpm, hnd $
    begin
      rw [show p = p^1, by simp [hp]],
      apply int.pow_dvd_of_le_of_pow_dvd _ hpm,
      apply nat.succ_le_of_lt hm
    end
else by simp [h, hp, padic_val]

lemma padic_val_eq_zero_of_not_dvd' {p : ℕ} {n : ℕ} (hnd : ¬ p ∣ n) : padic_val p n = 0 :=
by apply padic_val_eq_zero_of_not_dvd; simpa [int.coe_nat_dvd] using hnd

section padic_val
parameters (p : ℕ) [p_prime : prime p]

private lemma hpp : p > 1 := prime.gt_one p_prime

protected lemma mul {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
  padic_val p m + padic_val p n = padic_val p (m*n) :=
have m*n ≠ 0, from mul_ne_zero hm hn,
have hdivm : ↑(p ^ padic_val p m) ∣ m, from spec hpp hm,
have hdivn : ↑(p ^ padic_val p n) ∣ n, from spec hpp hn,
have hpoweq : (↑(p ^ (padic_val p m + padic_val p n)) : ℤ) =
                 (↑(p ^ padic_val p m * p ^ padic_val p n) : ℤ),
  by simp [nat.pow_add],
have hdiv : ↑(p ^ (padic_val p m + padic_val p n)) ∣ m*n,
  by rw [hpoweq, int.coe_nat_mul]; apply mul_dvd_mul; assumption,
have hall : ∀ k : ℕ, k > padic_val p m + padic_val p n → ¬ ↑(p ^ k) ∣ m*n, from
  assume (k : ℕ) (hkgt : k > padic_val p m + padic_val p n) (hdiv : ↑(p ^ k) ∣ m*n),
  have hpsucc : ↑(p ^ (padic_val p m + padic_val p n + 1)) ∣ m*n, from
    int.pow_dvd_of_le_of_pow_dvd hkgt hdiv,
  have hsd : _, from int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hdivm hdivn hpsucc,
  or.elim hsd
    (assume : ↑(p ^ (padic_val p m + 1)) ∣ m,
      is_greatest hpp hm _ (lt_succ_self _) this)
    (assume : ↑(p ^ (padic_val p n + 1)) ∣ n,
      is_greatest hpp hn _ (lt_succ_self _) this),
have habs : m.nat_abs * n.nat_abs = (m*n).nat_abs, by simp [int.nat_abs_mul],
begin
  simp only [habs] at *,
  apply unique,
  { apply hpp },
  repeat {assumption}
 end

include p_prime
protected lemma pow {q : ℤ} (hq : q ≠ 0) {k : ℕ} :
    padic_val p (q ^ k) = k * padic_val p q :=
begin
  induction k with k ih,
  { rw [_root_.pow_zero, zero_mul, padic_val.one (hpp p)] },
  rw [pow_succ', ← padic_val.mul (pow_ne_zero k hq) hq, succ_mul, ih]
end

end padic_val

section
variables {p : ℕ} (hp : p > 1)
include hp

lemma min_le_padic_val_add {m n : ℤ} (hmnz : m + n ≠ 0) :
  min (padic_val p m) (padic_val p n) ≤ padic_val p (m + n) :=
if hmz : m = 0 then by simp [hmz, nat.zero_le]
else if hnz : n = 0 then by simp [hnz, nat.zero_le]
else
  begin
    wlog hle := le_total (padic_val p m) (padic_val p n) using [n m],
    have hm : ∃ km, m = ↑(p ^ padic_val p m) * km, from spec hp hmz,
    have hn : ∃ kn, n = ↑(p ^ padic_val p n) * kn, from spec hp hnz,
    cases hm with km hkm,
    cases hn with kn hkn,
    have hmn : m + n = ↑(p ^ padic_val p m) * km + ↑(p ^ padic_val p n) * kn, by cc,
    have hmn' : m + n = ↑(p ^ padic_val p m) * (km + ↑(p ^ (padic_val p n - padic_val p m)) * kn),
    { rw [left_distrib, hmn, ←nat.pow_eq_mul_pow_sub _ hle], simp [mul_assoc] },
    have hpp : ↑(p ^ padic_val p m) ∣ (m + n),
    { rw hmn', apply dvd_mul_of_dvd_left, apply dvd_refl },
    have hpvle : padic_val p m ≤ padic_val p (m+n), from
      le_padic_val_of_pow_dvd hp hmnz hpp,
    transitivity,
    { apply min_le_left },
    { apply hpvle }
  end

lemma dvd_of_padic_val_pos {n : ℤ} (hpn : padic_val p n > 0) : ↑p ∣ n :=
if hn : n = 0 then by simp [hn]
else let hps := padic_val.spec hp hn in int.dvd_of_pow_dvd hpn hps


lemma padic_val_eq_zero_of_coprime {a b : ℕ} (hle : padic_val p a ≤ padic_val p b)
  (hab : nat.coprime a b) : padic_val p a = 0 :=
by_contradiction $ λ h,
  have hap : padic_val p a > 0, from nat.pos_of_ne_zero h,
  nat.not_coprime_of_dvd_of_dvd hp
    (int.coe_nat_dvd.1 (dvd_of_padic_val_pos hp hap))
    (int.coe_nat_dvd.1 (dvd_of_padic_val_pos hp (lt_of_lt_of_le hap hle)))
    hab

end
end padic_val

local infix `/.`:70 := rat.mk

def padic_val_rat (p : ℕ) (q : ℚ) : ℤ :=
(padic_val p q.num : ℤ) - (padic_val p q.denom : ℤ)

namespace padic_val_rat

section padic_val_rat
variables {p : ℕ} (hp : p > 1)
include hp

@[simp] protected lemma neg (q : ℚ) : padic_val_rat p (-q) = padic_val_rat p q :=
begin
  simp [padic_val_rat, hp]
end

@[simp] protected lemma one : padic_val_rat p 1 = 0 :=
have (1 : ℚ).num = 1, from rfl,
have (1 : ℚ).denom = 1, from rfl,
by simp [padic_val_rat, *]

@[simp] lemma padic_val_rat_self : padic_val_rat p p = 1 :=
by simp [padic_val_rat, hp]

lemma padic_val_rat_of_int (z : ℤ) : padic_val_rat p ↑z = padic_val p z :=
by simp [padic_val_rat, rat.coe_int_denom, padic_val.one hp]

end padic_val_rat

section padic_val_rat
open padic_val
variables (p : ℕ) [p_prime : prime p]
include p_prime

protected lemma defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) :
  padic_val_rat p q = (padic_val p n : ℤ) - padic_val p d :=
have hn : n ≠ 0, from rat.mk_num_ne_zero_of_ne_zero hqz qdf,
have hd : d ≠ 0, from rat.mk_denom_ne_zero_of_ne_zero hqz qdf,
have h : ∃ c : ℤ, n = c * q.num ∧ d = c * q.denom, from rat.num_denom_mk hn hd qdf,
have hqn : q.num ≠ 0, from rat.num_ne_zero_of_ne_zero hqz,
have hqd : (↑q.denom : ℤ) ≠ 0, by simp [rat.denom_ne_zero],
begin
  rcases h with ⟨c, ⟨hc1, hc2⟩⟩,
  have hcz : c ≠ 0,
    { intro hc,
      subst hc,
      apply hn, simpa using hc1 },
  unfold padic_val_rat,
  rw [hc1, hc2, ←padic_val.mul p hcz hqn, ←padic_val.mul p hcz hqd],
  simp [p_prime.gt_one], ring
end

protected lemma mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q*r) = padic_val_rat p q + padic_val_rat p r :=
have q*r = (q.num * r.num) /. (↑q.denom * ↑r.denom), by simp [rat.mul_num_denom],
begin
  rw padic_val_rat.defn p (mul_ne_zero hq hr) this,
  unfold padic_val_rat,
  rw [←padic_val.mul, ←padic_val.mul],
    {simp},
    repeat {apply int.coe_nat_ne_zero.2, apply ne_of_gt, apply rat.pos},
    repeat {apply rat.num_ne_zero_of_ne_zero, assumption}
end

protected lemma pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padic_val_rat p (q ^ k) = k * padic_val_rat p q :=
begin
  induction k with k ih,
  { rw [_root_.pow_zero, int.coe_nat_zero, zero_mul, padic_val_rat.one p_prime.gt_one] },
  rw [pow_succ', padic_val_rat.mul p (pow_ne_zero k hq) hq, int.coe_nat_succ, add_mul, ih, one_mul]
end

protected lemma div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q / r) = padic_val_rat p q - padic_val_rat p r :=
have hqr : q / r ≠ 0, from div_ne_zero hq hr,
have hnd' : _, from padic_val_rat.defn p hqr (rat.div_num_denom q r),
have _, from rat.denom_ne_zero q, have _, from rat.denom_ne_zero r,
begin
  rw [←padic_val.mul, ←padic_val.mul] at hnd',
  { simpa [padic_val_rat] using hnd' },
  all_goals { simpa <|> by apply rat.num_ne_zero_of_ne_zero; assumption }
end

theorem min_le_padic_val_rat_add {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
  min (padic_val_rat p q) (padic_val_rat p r) ≤ padic_val_rat p (q + r) :=
have hqn : q.num ≠ 0, from rat.num_ne_zero_of_ne_zero hq,
have hqd : q.denom ≠ 0, from rat.denom_ne_zero _,
have hrn : r.num ≠ 0, from rat.num_ne_zero_of_ne_zero hr,
have hrd : r.denom ≠ 0, from rat.denom_ne_zero _,
have hqdv : q.num /. q.denom ≠ 0, from rat.mk_ne_zero_of_ne_zero hqn (by simpa),
have hrdv : r.num /. r.denom ≠ 0, from rat.mk_ne_zero_of_ne_zero hrn (by simpa),
have hqreq : q + r = (((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ)),
  from calc
  q + r = (q.num /. q.denom + r.num /. r.denom) : by rw [←rat.num_denom q, ←rat.num_denom r]
    ... = (↑q.num : ℚ) / ↑q.denom + ((↑r.num : ℚ) / ↑r.denom) : by simp [rat.mk_eq_div]
    ... = (q.num * r.denom + q.denom * r.num) / (↑q.denom * ↑r.denom) :
      by rw div_add_div _ _ (show (q.denom : ℚ) ≠ 0, by simpa) (show (r.denom : ℚ) ≠ 0, by simpa)
    ... = ((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ) :
      by simp [rat.mk_eq_div],
have hsnz : q.num*r.denom + q.denom*r.num ≠ 0, from
  assume heq,
  have q + r = 0 /. (q.denom * r.denom), by rwa [heq] at hqreq,
  hqr (by simpa),
have hge  : (padic_val p (q.num * r.denom + q.denom * r.num) : ℤ) ≥
       min ((padic_val p (q.num*r.denom)) : ℤ)
           (padic_val p (q.denom*r.num)),
    from calc
    min ((padic_val p (q.num*r.denom)) : ℤ)
           (padic_val p (q.denom*r.num)) =
    (min (padic_val p (q.num*r.denom))
           (padic_val p (q.denom*r.num)) : ℤ) :
       by simp
     ... ≤ (padic_val p (q.num * r.denom + q.denom * r.num) : ℤ) :
       begin
         apply min_le_iff.2,
         simp only [int.coe_nat_le],
         apply min_le_iff.1,
         apply min_le_padic_val_add,
         exact p_prime.gt_one,
         assumption
       end,
calc
  padic_val_rat p (q + r)
         = padic_val_rat p
                         (((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ)) :
            by rw hqreq
     ... = padic_val p
                     (q.num * r.denom + q.denom * r.num) -
            padic_val p (↑q.denom * ↑r.denom) :
       begin apply padic_val_rat.defn p, cc, reflexivity end
     ... ≥ min (padic_val p (q.num*r.denom))
               (padic_val p (q.denom*r.num)) -
            padic_val p (↑q.denom * ↑r.denom) :
       sub_le_sub hge (le_refl _)
     ... = min (padic_val p q.num +
                 padic_val p r.denom)
               (padic_val p q.denom +
                 padic_val p r.num) -
            (padic_val p q.denom +
              padic_val p r.denom) :
       begin rw [←padic_val.mul, ←padic_val.mul, ←padic_val.mul], reflexivity,repeat {simpa <|> assumption} end
     ... = min (padic_val p q.num +
                 padic_val p r.denom -
                 (padic_val p q.denom +
                   padic_val p r.denom))
               (padic_val p q.denom +
                 padic_val p r.num -
                 (padic_val p q.denom +
                   padic_val p r.denom)) :
       by apply min_sub
     ... = min (padic_val p q.num -
                 padic_val p q.denom)
               (padic_val p r.num -
                 padic_val p r.denom) :
       by simp
     ... = min (padic_val_rat p (q.num /. ↑q.denom))
               (padic_val_rat p (r.num /. ↑r.denom)) :
       by rw [padic_val_rat.defn p, padic_val_rat.defn p]; simp *
     ... = min (padic_val_rat p q)
               (padic_val_rat p r) :
       by rw [←rat.num_denom q, ←rat.num_denom r]
end padic_val_rat
end padic_val_rat


def padic_norm (p : ℕ) (q : ℚ) : ℚ :=
if q = 0 then 0 else fpow (↑p : ℚ) (-(padic_val_rat p q))

namespace padic_norm

section padic_norm
open padic_val_rat
variables (p : ℕ) [hp : prime p]
include hp

@[simp] protected lemma zero : padic_norm p 0 = 0 := by simp [padic_norm]

@[simp] protected lemma eq_fpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
  padic_norm p q = fpow p (-(padic_val_rat p q)) :=
by simp [hq, padic_norm]

protected lemma nonzero {q : ℚ} (hq : q ≠ 0) : padic_norm p q ≠ 0 :=
begin
  rw padic_norm.eq_fpow_of_nonzero p hq,
  apply fpow_ne_zero_of_ne_zero, simp,
  apply ne_of_gt,
  simpa using hp.pos
end

@[simp] protected lemma neg (q : ℚ) : padic_norm p (-q) = padic_norm p q :=
if hq : q = 0 then by simp [hq]
else by simp [padic_norm, hq, hp.gt_one]

lemma zero_of_padic_norm_eq_zero {q : ℚ} (h : padic_norm p q = 0) : q = 0 :=
by_contradiction $
  assume hq : q ≠ 0,
  have padic_norm p q = fpow p (-(padic_val_rat p q)), by simp [hq],
  fpow_ne_zero_of_ne_zero
    (show (↑p : ℚ) ≠ 0, by simp [prime.ne_zero hp])
    (-(padic_val_rat p q)) (by rw [←this, h])

protected lemma nonneg (q : ℚ) : padic_norm p q ≥ 0 :=
if hq : q = 0 then by simp [hq]
else
  begin
    unfold padic_norm; split_ifs,
    apply fpow_nonneg_of_nonneg,
    apply nat.cast_nonneg
  end

@[simp] protected theorem mul (q r : ℚ) : padic_norm p (q*r) = padic_norm p q * padic_norm p r :=
if hq : q = 0 then
  by simp [hq]
else if hr : r = 0 then
  by simp [hr]
else
  have q*r ≠ 0, from mul_ne_zero hq hr,
  have (↑p : ℚ) ≠ 0, by simp [prime.ne_zero hp],
  by simp [padic_norm, *, padic_val_rat.mul, fpow_add this]

@[simp] protected theorem div (q r : ℚ) : padic_norm p (q / r) = padic_norm p q / padic_norm p r :=
if hr : r = 0 then by simp [hr] else
eq_div_of_mul_eq _ _ (padic_norm.nonzero _ hr) (by rw [←padic_norm.mul, div_mul_cancel _ hr])

protected theorem of_int (z : ℤ) : padic_norm p ↑z ≤ 1 :=
if hz : z = 0 then by simp [hz] else
begin
  suffices : padic_norm p ↑z = fpow (↑p : ℚ) (-(padic_val p z)),
  { convert fpow_le_one_of_nonpos (show (↑p : ℚ) ≥ ↑(1 : ℕ), from _) _,
    { apply le_of_lt, apply nat.cast_lt.2 hp.gt_one },
    apply neg_nonpos.2,
    apply int.coe_nat_nonneg },
  have hnz : padic_val_rat p z = padic_val p z, from padic_val_rat_of_int hp.gt_one z,
  simp [padic_val_rat, hz, hnz]
end

--TODO: p implicit
private lemma nonarchimedean_aux {q r : ℚ} (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
have hnqp : padic_norm p q ≥ 0, from padic_norm.nonneg _ _,
have hnrp : padic_norm p r ≥ 0, from padic_norm.nonneg _ _,
if hq : q = 0 then
  by simp [hq, max_eq_right hnrp]
else if hr : r = 0 then
  by simp [hr, max_eq_left hnqp]
else if hqr : q + r = 0 then
  le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
else
  begin
    unfold padic_norm, split_ifs,
    apply le_max_iff.2,
    left,
    have hpge1 : (↑p : ℚ) ≥ ↑(1 : ℕ), from (nat.cast_le.2 $ le_of_lt $ prime.gt_one hp),
    apply fpow_le_of_le hpge1,
    apply neg_le_neg,
    have : padic_val_rat p q =
            min (padic_val_rat p q) (padic_val_rat p r),
      from (min_eq_left h).symm,
    rw this,
    apply min_le_padic_val_rat_add; assumption
  end

protected theorem nonarchimedean {q r : ℚ} :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
begin
    wlog hle := le_total (padic_val_rat p q) (padic_val_rat p r) using [q r],
    exact nonarchimedean_aux p hle
end

theorem triangle_ineq (q r : ℚ) : padic_norm p (q + r) ≤ padic_norm p q + padic_norm p r :=
calc padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) : padic_norm.nonarchimedean p
                       ... ≤ padic_norm p q + padic_norm p r :
                         max_le_add_of_nonneg (padic_norm.nonneg p _) (padic_norm.nonneg p _)

protected theorem sub {q r : ℚ} : padic_norm p (q - r) ≤ max (padic_norm p q) (padic_norm p r) :=
by rw [sub_eq_add_neg, ←padic_norm.neg p r]; apply padic_norm.nonarchimedean

lemma add_eq_max_of_ne {q r : ℚ} (hne : padic_norm p q ≠ padic_norm p r) :
  padic_norm p (q + r) = max (padic_norm p q) (padic_norm p r) :=
begin
  wlog hle := le_total (padic_norm p r) (padic_norm p q) using [q r],
  have hlt : padic_norm p r < padic_norm p q, from lt_of_le_of_ne hle hne.symm,
  have : padic_norm p q ≤ max (padic_norm p (q + r)) (padic_norm p r), from calc
   padic_norm p q = padic_norm p (q + r - r) : by congr; ring
               ... ≤ max (padic_norm p (q + r)) (padic_norm p (-r)) : padic_norm.nonarchimedean p
               ... = max (padic_norm p (q + r)) (padic_norm p r) : by simp,
  have hnge : padic_norm p r ≤ padic_norm p (q + r),
  { apply le_of_not_gt,
    intro hgt,
    rw max_eq_right_of_lt hgt at this,
    apply not_lt_of_ge this,
    assumption },
  have : padic_norm p q ≤ padic_norm p (q + r), by rwa [max_eq_left hnge] at this,
  apply _root_.le_antisymm,
  { apply padic_norm.nonarchimedean p },
  { rw max_eq_left_of_lt hlt,
    assumption }
end

protected theorem image {q : ℚ} (hq : q ≠ 0) : ∃ n : ℤ, padic_norm p q = fpow p (-n) :=
⟨ (padic_val_rat p q), by simp [padic_norm, hq] ⟩

instance : is_absolute_value (padic_norm p) :=
{ abv_nonneg := padic_norm.nonneg p,
  abv_eq_zero :=
    begin
      intros,
      constructor; intro,
      { apply zero_of_padic_norm_eq_zero p, assumption },
      { simp [*] }
    end,
  abv_add := padic_norm.triangle_ineq p,
  abv_mul := padic_norm.mul p }

lemma le_of_dvd {n : ℕ} {z : ℤ} (hd : ↑(p^n) ∣ z) : padic_norm p z ≤ fpow ↑p (-n) :=
have hp' : (↑p : ℚ) ≥ 1, from show ↑p ≥ ↑(1 : ℕ), from cast_le.2 (le_of_lt hp.gt_one),
have hpn : (↑p : ℚ) ≥ 0, from le_trans zero_le_one hp',
begin
  unfold padic_norm, split_ifs with hz hz,
  { simpa [padic_norm, hz] using fpow_nonneg_of_nonneg hpn _ },
  { apply fpow_le_of_le hp',
    apply neg_le_neg,
    rw padic_val_rat_of_int hp.gt_one _,
    apply int.coe_nat_le.2,
    apply padic_val.le_padic_val_of_pow_dvd hp.gt_one,
    { simpa using hz },
    { assumption }}
end

end padic_norm
end padic_norm
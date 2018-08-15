/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic valuation on ℤ and ℚ, and the p-adic norm on ℚ
-/

import data.rat algebra.field_power
import tactic.wlog tactic.ring

universe u 
open nat

private lemma exi_div (p : ℕ) (n : ℤ) : ∃ k : ℕ, ↑(p ^ k) ∣ n := ⟨0, by simp⟩

private lemma bound {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) : 
        ∀ k : ℕ, k > n.nat_abs → ¬ (↑(p ^ k) ∣ n) := 
assume k (hkn : k > n.nat_abs),
have n.nat_abs < p^k, from lt.trans (le_pow_self hp _) (pow_lt_pow_of_lt_right hp hkn),
assume hdvd : ↑(p ^ k) ∣ n,
have hdvd' : (p ^ k) ∣ n.nat_abs, from int.dvd_nat_abs_of_of_nat_dvd hdvd,
let hle := le_of_dvd (int.nat_abs_pos_of_ne_zero hn) hdvd' in 
not_le_of_gt this hle 

def padic_val {p : ℕ} (hp : p > 1) (n : ℤ) : ℕ := 
if hn : n = 0 then
  0
else nat.find_greatest (bound hp hn) (exi_div p n)

namespace padic_val 

lemma spec {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) : ↑(p ^ padic_val hp n) ∣ n := 
let ha := nat.find_greatest_spec (bound hp hn) (exi_div p n) in
by simpa [padic_val, hn] using ha

lemma is_greatest {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) : 
      ∀ m : ℕ, m > padic_val hp n → ¬ ↑(p ^ m) ∣ n :=
let ha := nat.find_greatest_is_greatest (bound hp hn) (exi_div p n) in 
by simpa [padic_val, hn] using ha

lemma unique {p : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) {k : ℕ} (hk : ↑(p^k) ∣ n) 
      (hall : ∀ m : ℕ, m > k → ¬ ↑(p^m) ∣ n) : k = padic_val hp n :=
let ha := nat.find_greatest_unique (bound hp hn) (exi_div p n) hk hall in 
by simpa [padic_val, hn] using ha

@[simp] protected lemma neg {p : ℕ} (hp : p > 1) (n : ℤ) : padic_val hp (-n) = padic_val hp n :=
if hn : n = 0 then by simp [hn] else 
have hnn : -n ≠ 0, by simp [hn],
unique hp hn
  (have ↑(p ^ padic_val hp (-n)) ∣ (-n), from spec hp hnn, dvd_of_dvd_neg this) 
  (assume m hm (hdiv : (↑(p^m) ∣ n)), 
   have ↑(p^m) ∣ (-n), from dvd_neg_of_dvd hdiv, 
   is_greatest hp  hnn _ hm this)

lemma le_padic_val_of_pow_div {p k : ℕ} (hp : p > 1) {n : ℤ} (hn : n ≠ 0) (h : ↑(p^k) ∣ n) : 
      k ≤ padic_val hp n := 
le_of_not_gt $
  assume : k > padic_val hp n,
  is_greatest hp hn _ this h

section
variables {p : ℕ} (hp : p > 1)

@[simp] protected lemma zero : padic_val hp 0 = 0 := by simp [padic_val]

@[simp] protected lemma one : padic_val hp 1 = 0 :=
begin
  symmetry,
  apply nat.find_greatest_unique,
    { norm_num },
    { intros k hk,
      have h1k : 1 ^ k < p ^ k, from pow_lt_pow_of_lt_left hp hk,
      rw nat.one_pow at h1k,
      intro hdvd,
      apply not_le_of_gt h1k,
      apply le_of_dvd zero_lt_one,
      apply int.coe_nat_dvd.1 hdvd }
end 

@[simp] lemma padic_val_self : padic_val hp p = 1 :=
have h : p ≠ 0, by intro h'; subst h'; exact absurd hp dec_trivial,
begin 
  unfold padic_val,
  simp [h],
  symmetry,
  apply nat.find_greatest_unique,
    { simp },
    { intros k hk hdvd,
      apply not_pos_pow_dvd hp hk,
      rw ←int.coe_nat_dvd, simpa }
end 

end

section padic_val 
parameters {p : ℕ} (p_prime : prime p)

private lemma hpp : p > 1 := prime.gt_one p_prime

protected lemma mul {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) : 
      padic_val hpp m + padic_val hpp n = padic_val hpp (m*n) :=
have m*n ≠ 0, from mul_ne_zero hm hn,
have hdivm : ↑(p ^ padic_val hpp m) ∣ m, from spec hpp hm,
have hdivn : ↑(p ^ padic_val hpp n) ∣ n, from spec hpp hn,
have hdiv : ↑(p ^ (padic_val hpp m + padic_val hpp n)) ∣ m*n, from
  have hpoweq : (↑(p ^ (padic_val hpp m + padic_val hpp n)) : ℤ) = 
                 (↑(p ^ padic_val hpp m * p ^ padic_val hpp n) : ℤ),
    by simp [nat.pow_add],
  begin
    rw [hpoweq, int.coe_nat_mul],
    apply mul_dvd_mul,
    repeat {assumption}
  end, 
have hall : ∀ k : ℕ, k > padic_val hpp m + padic_val hpp n → ¬ ↑(p ^ k) ∣ m*n, from
  assume (k : ℕ) (hkgt : k > padic_val hpp m + padic_val hpp n) (hdiv : ↑(p ^ k) ∣ m*n),
  have hpsucc : ↑(p ^ (padic_val hpp m + padic_val hpp n + 1)) ∣ m*n, from
    int.pow_div_of_le_of_pow_div_int hkgt hdiv,
  let hsd := succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int p_prime hdivm hdivn hpsucc in
  or.elim hsd
    (assume : ↑(p ^ (padic_val hpp m + 1)) ∣ m,
      is_greatest hpp hm _ (lt_succ_self _) this)
    (assume : ↑(p ^ (padic_val hpp n + 1)) ∣ n,
      is_greatest hpp hn _ (lt_succ_self _) this), 
have habs : m.nat_abs * n.nat_abs = (m*n).nat_abs, by simp [int.nat_abs_mul],
begin 
  simp only [habs] at *, 
  apply unique, 
  repeat {assumption}
 end 

end padic_val 

section
variables {p : ℕ} (hp : p > 1)

lemma min_le_padic_val_add {m n : ℤ} (hmnz : m + n ≠ 0) : 
      min (padic_val hp m) (padic_val hp n) ≤ padic_val hp (m + n) :=
if hmz : m = 0 then by simp [hmz, nat.zero_le]
else if hnz : n = 0 then by simp [hnz, nat.zero_le]
else 
  begin
    wlog hle := le_total (padic_val hp m) (padic_val hp n) using [n m],
    have hm : ∃ km, m = ↑(p ^ padic_val hp m) * km, from spec hp hmz,
    have hn : ∃ kn, n = ↑(p ^ padic_val hp n) * kn, from spec hp hnz,
    cases hm with km hkm,
    cases hn with kn hkn,
    have hmn : m + n = ↑(p ^ padic_val hp m) * km + ↑(p ^ padic_val hp n) * kn, by cc,
    have hmn' : m + n = ↑(p ^ padic_val hp m) * (km + ↑(p ^ (padic_val hp n - padic_val hp m)) * kn), 
      { rw [left_distrib, hmn, ←nat.pow_eq_mul_pow_sub _ hle], simp [mul_assoc] },
    have hpp : ↑(p ^ padic_val hp m) ∣ (m + n),
      { rw hmn', apply dvd_mul_of_dvd_left, apply dvd_refl },
    have hpvle : padic_val hp m ≤ padic_val hp (m+n), from 
      le_padic_val_of_pow_div _ hmnz hpp,
    transitivity,
      { apply min_le_left },
      { apply hpvle }
  end 

end
end padic_val 

local infix `/.`:70 := rat.mk

def padic_val_rat {p : ℕ} (hp : p > 1) (q : ℚ) : ℤ :=
(padic_val hp q.num : ℤ) - (padic_val hp q.denom : ℤ)

namespace padic_val_rat

section padic_val_rat
variables {p : ℕ} (hp : p > 1)

@[simp] protected lemma neg (q : ℚ) : padic_val_rat hp (-q) = padic_val_rat hp q :=
begin 
  simp [padic_val_rat]
end 

@[simp] protected lemma one : padic_val_rat hp 1 = 0 :=
have (1 : ℚ).num = 1, from rfl,
have (1 : ℚ).denom = 1, from rfl,
by simp [padic_val_rat, *]

@[simp] lemma padic_val_rat_self : padic_val_rat hp p = 1 :=
by simp [padic_val_rat]

end padic_val_rat 

section padic_val_rat
open padic_val
variables {p : ℕ} (p_prime : prime p)

protected lemma defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) : 
      padic_val_rat (prime.gt_one p_prime) q = 
        (padic_val (prime.gt_one p_prime) n : ℤ) - padic_val (prime.gt_one p_prime) d :=
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
  rw [hc1, hc2, ←padic_val.mul p_prime hcz hqn, ←padic_val.mul p_prime hcz hqd],
  simp
end

protected lemma mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : 
        padic_val_rat (prime.gt_one p_prime) (q*r) = 
          padic_val_rat (prime.gt_one p_prime) q + padic_val_rat (prime.gt_one p_prime) r :=
have q*r = (q.num * r.num) /. (↑q.denom * ↑r.denom), by simp [rat.mul_num_denom],
begin
  rw padic_val_rat.defn p_prime (mul_ne_zero hq hr) this,
  unfold padic_val_rat,
  rw [←padic_val.mul p_prime, ←padic_val.mul p_prime],
    {simp},
    repeat {apply int.coe_nat_ne_zero.2, apply ne_of_gt, apply rat.pos},
    repeat {apply rat.num_ne_zero_of_ne_zero, assumption}
end  

theorem min_le_padic_val_rat_add {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
        min (padic_val_rat (prime.gt_one p_prime) q) (padic_val_rat (prime.gt_one p_prime) r) ≤ 
          padic_val_rat (prime.gt_one p_prime) (q + r) :=
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
have hge  : (padic_val (prime.gt_one p_prime) (q.num * r.denom + q.denom * r.num) : ℤ) ≥ 
       min ((padic_val (prime.gt_one p_prime) (q.num*r.denom)) : ℤ) 
           (padic_val (prime.gt_one p_prime) (q.denom*r.num)),
    from calc 
    min ((padic_val (prime.gt_one p_prime) (q.num*r.denom)) : ℤ) 
           (padic_val (prime.gt_one p_prime) (q.denom*r.num)) = 
    (min (padic_val (prime.gt_one p_prime) (q.num*r.denom)) 
           (padic_val (prime.gt_one p_prime) (q.denom*r.num)) : ℤ) :
       by simp
     ... ≤ (padic_val (prime.gt_one p_prime) (q.num * r.denom + q.denom * r.num) : ℤ) : 
       begin 
         apply min_le_iff.2, 
         simp only [int.coe_nat_le], 
         apply min_le_iff.1, 
         apply min_le_padic_val_add, 
         assumption 
       end,  
calc 
  padic_val_rat (prime.gt_one p_prime) (q + r) 
         = padic_val_rat (prime.gt_one p_prime) 
                         (((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ)) :
            by rw hqreq
     ... = padic_val (prime.gt_one p_prime) 
                     (q.num * r.denom + q.denom * r.num) - 
            padic_val (prime.gt_one p_prime) (↑q.denom * ↑r.denom) :
       begin apply padic_val_rat.defn, cc, reflexivity end 
     ... ≥ min (padic_val (prime.gt_one p_prime) (q.num*r.denom)) 
               (padic_val (prime.gt_one p_prime) (q.denom*r.num)) - 
            padic_val (prime.gt_one p_prime) (↑q.denom * ↑r.denom) :
       sub_le_sub hge (le_refl _)
     ... = min (padic_val (prime.gt_one p_prime) q.num + 
                 padic_val (prime.gt_one p_prime) r.denom) 
               (padic_val (prime.gt_one p_prime) q.denom + 
                 padic_val (prime.gt_one p_prime) r.num) - 
            (padic_val (prime.gt_one p_prime) q.denom + 
              padic_val (prime.gt_one p_prime) r.denom) :
       begin rw [←padic_val.mul, ←padic_val.mul, ←padic_val.mul], reflexivity, repeat {simpa} end
     ... = min (padic_val (prime.gt_one p_prime) q.num + 
                 padic_val (prime.gt_one p_prime) r.denom - 
                 (padic_val (prime.gt_one p_prime) q.denom + 
                   padic_val (prime.gt_one p_prime) r.denom)) 
               (padic_val (prime.gt_one p_prime) q.denom + 
                 padic_val (prime.gt_one p_prime) r.num - 
                 (padic_val (prime.gt_one p_prime) q.denom + 
                   padic_val (prime.gt_one p_prime) r.denom)) :
       by apply min_add_eq_min_add_min
     ... = min (padic_val (prime.gt_one p_prime) q.num - 
                 padic_val (prime.gt_one p_prime) q.denom) 
               (padic_val (prime.gt_one p_prime) r.num - 
                 padic_val (prime.gt_one p_prime) r.denom) :
       by simp
     ... = min (padic_val_rat (prime.gt_one p_prime) (q.num /. ↑q.denom)) 
               (padic_val_rat (prime.gt_one p_prime) (r.num /. ↑r.denom)) : 
       by rw [padic_val_rat.defn, padic_val_rat.defn]; simpa
     ... = min (padic_val_rat (prime.gt_one p_prime) q) 
               (padic_val_rat (prime.gt_one p_prime) r) : 
       by rw [←rat.num_denom q, ←rat.num_denom r]
end padic_val_rat 
end padic_val_rat 

def padic_norm {p : ℕ} (hp : prime p) (q : ℚ) : ℚ :=
if q = 0 then 0 
else fpow (↑p : ℚ) (-(padic_val_rat (prime.gt_one hp) q))

namespace padic_norm

section padic_norm
open padic_val_rat
variables {p : ℕ} (hp : prime p)

@[simp] protected lemma zero : padic_norm hp 0 = 0 := by simp [padic_norm]

@[simp] protected lemma nonzero {q : ℚ} (hq : q ≠ 0) : 
        padic_norm hp q = fpow p (-(padic_val_rat (prime.gt_one hp) q)) :=
by simp [hq, padic_norm]

@[simp] protected lemma neg (q : ℚ) : padic_norm hp (-q) = padic_norm hp q :=
if hq : q = 0 then by simp [hq] 
else by simp [padic_norm, hq]

lemma zero_of_padic_norm_eq_zero {q : ℚ} (h : padic_norm hp q = 0) : q = 0 :=
by_contradiction $
  assume hq : q ≠ 0,
  have padic_norm hp q = fpow p (-(padic_val_rat (prime.gt_one hp) q)), by simp [hq],
  fpow_ne_zero_of_ne_zero 
    (show (↑p : ℚ) ≠ 0, by simp [prime.ne_zero hp]) 
    (-(padic_val_rat (prime.gt_one hp) q)) (by rw [←this, h])

protected lemma nonneg (q : ℚ) : padic_norm hp q ≥ 0 :=
if hq : q = 0 then by simp [hq]
else 
  begin 
    unfold padic_norm; split_ifs,
    apply fpow_nonneg_of_nonneg,
    apply nat.cast_nonneg 
  end 

protected theorem mul (q r : ℚ) : padic_norm hp (q*r) = padic_norm hp q * padic_norm hp r :=
if hq : q = 0 then
  by simp [hq]
else if hr : r = 0 then
  by simp [hr]
else
  have q*r ≠ 0, from mul_ne_zero hq hr,
  have (↑p : ℚ) ≠ 0, by simpa [prime.ne_zero hp],
  by simp [padic_norm, *, padic_val_rat.mul, fpow_add this]

theorem triangle_ineq (q r : ℚ) : padic_norm hp (q + r) ≤ padic_norm hp q + padic_norm hp r :=
if hq : q = 0 then 
  by simp [hq]
else if hr : r = 0 then
  by simp [hr]
else if hqr : q + r = 0 then
  begin simp [hqr], apply add_nonneg; apply padic_norm.nonneg end 
else 
  have hminle : min (padic_val_rat (prime.gt_one hp) q) (padic_val_rat (prime.gt_one hp) r) ≤ 
                 (padic_val_rat (prime.gt_one hp) (q + r)),
    by apply min_le_padic_val_rat_add; assumption,
  have hpge1 : (↑p : ℚ) ≥ ↑(1 : ℕ), from nat.cast_le.2 $ le_of_lt $ prime.gt_one hp,
  calc 
    padic_norm hp (q + r) = fpow p (-(padic_val_rat (prime.gt_one hp) (q + r))) : 
                       by simp [padic_norm, *]
                      ... ≤ max (fpow p (-(padic_val_rat (prime.gt_one hp) q))) 
                                ((fpow p (-(padic_val_rat (prime.gt_one hp) r)))) : 
                       pow_le_max_of_min_le hpge1 hminle
                      ... = max (padic_norm hp q) (padic_norm hp r) : by simp [padic_norm, *] 
                      ... ≤ padic_norm hp q + padic_norm hp r : 
                       by apply max_le_add_of_nonneg; apply padic_norm.nonneg

private lemma nonarchimedean_aux {q r : ℚ}
        (h : padic_val_rat (prime.gt_one hp) q ≤ padic_val_rat (prime.gt_one hp) r) : 
        padic_norm hp (q + r) ≤ max (padic_norm hp q) (padic_norm hp r) :=
have hnqp : padic_norm hp q ≥ 0, from padic_norm.nonneg _ _,
have hnrp : padic_norm hp r ≥ 0, from padic_norm.nonneg _ _,
if hq : q = 0 then
  by simp [hq, max_eq_right hnrp]
else if hr : r = 0 then
  by simp [hr, max_eq_left hnqp]
else if hqr : q + r = 0 then
  le_trans (by simpa [hqr] using padic_norm.nonneg hp) (le_max_left _ _)
else
  begin 
    unfold padic_norm, split_ifs,
    apply le_max_iff.2,
    left,
    have hpge1 : (↑p : ℚ) ≥ ↑(1 : ℕ), from (nat.cast_le.2 $ le_of_lt $ prime.gt_one hp),
    apply fpow_le_of_le hpge1,
    apply neg_le_neg,
    have : padic_val_rat (prime.gt_one hp) q = 
            min (padic_val_rat (prime.gt_one hp) q) (padic_val_rat (prime.gt_one hp) r),
      from (min_eq_left h).symm,
    rw this,
    apply min_le_padic_val_rat_add; assumption
  end 

protected theorem nonarchimedean {q r : ℚ} : 
        padic_norm hp (q + r) ≤ max (padic_norm hp q) (padic_norm hp r) :=
if h : padic_val_rat (prime.gt_one hp) q ≤ padic_val_rat (prime.gt_one hp) r then
  nonarchimedean_aux hp h
else 
  have h' : padic_val_rat (prime.gt_one hp) r ≤ padic_val_rat (prime.gt_one hp) q,
    from le_of_lt $ lt_of_not_ge h,
  let h'' := nonarchimedean_aux hp h' in
  by rwa [add_comm, max_comm] at h''

lemma add_eq_max_of_ne {q r : ℚ} (hne : padic_norm hp q ≠ padic_norm hp r) : 
      padic_norm hp (q + r) = max (padic_norm hp q) (padic_norm hp r) :=
begin
  wlog hle := le_total (padic_norm hp r) (padic_norm hp q) using [q r],
  have hlt : padic_norm hp r < padic_norm hp q, from lt_of_le_of_ne hle hne.symm,
  have : padic_norm hp q ≤ max (padic_norm hp (q + r)) (padic_norm hp r), from calc
   padic_norm hp q = padic_norm hp (q + r - r) : by congr; ring
               ... ≤ max (padic_norm hp (q + r)) (padic_norm hp (-r)) : padic_norm.nonarchimedean hp
               ... = max (padic_norm hp (q + r)) (padic_norm hp r) : by simpa,
  have hnge : padic_norm hp r ≤ padic_norm hp (q + r), 
    { apply le_of_not_gt,
      intro hgt,
      rw max_eq_right_of_lt hgt at this,
      apply not_lt_of_ge this,
      assumption },
  have : padic_norm hp q ≤ padic_norm hp (q + r), by rwa [max_eq_left hnge] at this,
  apply _root_.le_antisymm,
    { apply padic_norm.nonarchimedean hp },
    { rw max_eq_left_of_lt hlt,
      assumption }
end 

protected theorem image {q : ℚ} (hq : q ≠ 0) : ∃ n : ℤ, padic_norm hp q = fpow p (-n) :=
⟨ (padic_val_rat (prime.gt_one hp) q), by simp [padic_norm, hq] ⟩ 

instance : is_absolute_value (padic_norm hp) :=
{ abv_nonneg := padic_norm.nonneg hp,
  abv_eq_zero := 
    begin 
      intros, 
      constructor; intro, 
        { apply zero_of_padic_norm_eq_zero hp, assumption }, 
        { simp [*] } 
    end,
  abv_add := padic_norm.triangle_ineq hp,
  abv_mul := padic_norm.mul hp }

end padic_norm 
end padic_norm
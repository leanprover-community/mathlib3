/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic valuation on ℤ and ℚ, and the p-adic norm on ℚ
-/

import data.rat algebra.gcd_domain algebra.field_power
import ring_theory.multiplicity tactic.ring

universe u

open nat

attribute [class] nat.prime

local infix `/.`:70 := rat.mk

open multiplicity

def padic_val_rat (p : ℕ) (q : ℚ) : ℤ :=
if h : q ≠ 0 ∧ p ≠ 1
then (multiplicity (p : ℤ) q.num).get
    (multiplicity.finite_int_iff.2 ⟨h.2, rat.num_ne_zero_of_ne_zero h.1⟩) -
  (multiplicity (p : ℤ) q.denom).get
    (multiplicity.finite_int_iff.2 ⟨h.2, ne.symm $ ne_of_lt (int.coe_nat_pos.2 q.3)⟩)
else 0

lemma padic_val_rat_def (p : ℕ) [hp : p.prime] {q : ℚ} (hq : q ≠ 0) : padic_val_rat p q =
  (multiplicity (p : ℤ) q.num).get (finite_int_iff.2 ⟨hp.ne_one, rat.num_ne_zero_of_ne_zero hq⟩) -
  (multiplicity (p : ℤ) q.denom).get (finite_int_iff.2 ⟨hp.ne_one, int.coe_nat_ne_zero_iff_pos.2 q.3⟩) :=
dif_pos ⟨hq, hp.ne_one⟩

namespace padic_val_rat
open multiplicity
section padic_val_rat
variables {p : ℕ}

@[simp] protected lemma neg (q : ℚ) : padic_val_rat p (-q) = padic_val_rat p q :=
begin
  unfold padic_val_rat,
  split_ifs,
  { simp [-add_comm]; refl },
  { exfalso, simp * at * },
  { exfalso, simp * at * },
  { refl }
end

@[simp] protected lemma one : padic_val_rat p 1 = 0 :=
by unfold padic_val_rat; split_ifs; simp *

@[simp] lemma padic_val_rat_self (hp : 1 < p) : padic_val_rat p p = 1 :=
by unfold padic_val_rat; split_ifs; simp [*, nat.one_lt_iff_ne_zero_and_ne_one] at *

lemma padic_val_rat_of_int (z : ℤ) (hp : p ≠ 1) (hz : z ≠ 0) :
  padic_val_rat p (z : ℚ) = (multiplicity (p : ℤ) z).get
    (finite_int_iff.2 ⟨hp, hz⟩) :=
by rw [padic_val_rat, dif_pos]; simp *; refl

end padic_val_rat

section padic_val_rat
open multiplicity
variables (p : ℕ) [p_prime : nat.prime p]
include p_prime

lemma finite_int_prime_iff {p : ℕ} [p_prime : p.prime] {a : ℤ} : finite (p : ℤ) a ↔ a ≠ 0 :=
by simp [finite_int_iff, ne.symm (ne_of_lt (p_prime.gt_one))]

protected lemma defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) :
  padic_val_rat p q = (multiplicity (p : ℤ) n).get (finite_int_iff.2
    ⟨ne.symm $ ne_of_lt p_prime.gt_one, λ hn, by simp * at *⟩) -
  (multiplicity (p : ℤ) d).get (finite_int_iff.2 ⟨ne.symm $ ne_of_lt p_prime.gt_one,
    λ hd, by simp * at *⟩) :=
have hn : n ≠ 0, from rat.mk_num_ne_zero_of_ne_zero hqz qdf,
have hd : d ≠ 0, from rat.mk_denom_ne_zero_of_ne_zero hqz qdf,
let ⟨c, hc1, hc2⟩ := rat.num_denom_mk hn hd qdf in
by rw [padic_val_rat, dif_pos];
  simp [hc1, hc2, multiplicity.mul' (nat.prime_iff_prime_int.1 p_prime),
    (ne.symm (ne_of_lt p_prime.gt_one)), hqz]

protected lemma mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q * r) = padic_val_rat p q + padic_val_rat p r :=
have q*r = (q.num * r.num) /. (↑q.denom * ↑r.denom),
  by rw [rat.mul_num_denom, int.coe_nat_mul],
have hq' : q.num /. q.denom ≠ 0, by rw ← rat.num_denom q; exact hq,
have hr' : r.num /. r.denom ≠ 0, by rw ← rat.num_denom r; exact hr,
have hp' : _root_.prime (p : ℤ), from nat.prime_iff_prime_int.1 p_prime,
begin
  rw [padic_val_rat.defn p (mul_ne_zero hq hr) this],
  conv_rhs { rw [rat.num_denom q, padic_val_rat.defn p hq',
    rat.num_denom r, padic_val_rat.defn p hr'] },
  rw [multiplicity.mul' hp', multiplicity.mul' hp']; simp
end

protected lemma pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padic_val_rat p (q ^ k) = k * padic_val_rat p q :=
by induction k; simp [*, padic_val_rat.mul _ hq (pow_ne_zero _ hq),
  _root_.pow_succ, add_mul]

protected lemma inv {q : ℚ} (hq : q ≠ 0) :
  padic_val_rat p (q⁻¹) = -padic_val_rat p q :=
by rw [eq_neg_iff_add_eq_zero, ← padic_val_rat.mul p (inv_ne_zero hq) hq,
    inv_mul_cancel hq, padic_val_rat.one]

protected lemma div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q / r) = padic_val_rat p q - padic_val_rat p r :=
by rw [div_eq_mul_inv, padic_val_rat.mul p hq (inv_ne_zero hr),
    padic_val_rat.inv p hr, sub_eq_add_neg]

lemma padic_val_rat_le_padic_val_rat_iff {n₁ n₂ d₁ d₂ : ℤ}
  (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
  padic_val_rat p (n₁ /. d₁) ≤ padic_val_rat p (n₂ /. d₂) ↔
  ∀ (n : ℕ), ↑p ^ n ∣ n₁ * d₂ → ↑p ^ n ∣ n₂ * d₁ :=
have hf1 : finite (p : ℤ) (n₁ * d₂),
  from finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂),
have hf2 : finite (p : ℤ) (n₂ * d₁),
  from finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁),
by conv {to_lhs, rw [padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₁ hd₁) rfl,
    padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₂ hd₂) rfl,
    sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le,
    ← int.coe_nat_add, ← int.coe_nat_add, int.coe_nat_le,
    ← multiplicity.mul' (nat.prime_iff_prime_int.1 p_prime) hf1, add_comm,
    ← multiplicity.mul' (nat.prime_iff_prime_int.1 p_prime) hf2,
    enat.get_le_get, multiplicity_le_multiplicity_iff] }

theorem le_padic_val_rat_add_of_le {q r : ℚ}
  (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0)
  (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_val_rat p q ≤ padic_val_rat p (q + r) :=
have hqn : q.num ≠ 0, from rat.num_ne_zero_of_ne_zero hq,
have hqd : (q.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero.2 $ rat.denom_ne_zero _,
have hrn : r.num ≠ 0, from rat.num_ne_zero_of_ne_zero hr,
have hrd : (r.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero.2 $ rat.denom_ne_zero _,
have hqdv : q.num /. q.denom ≠ 0, from rat.mk_ne_zero_of_ne_zero hqn hqd,
have hrdv : r.num /. r.denom ≠ 0, from rat.mk_ne_zero_of_ne_zero hrn hrd,
have hqreq : q + r = (((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ)),
  from rat.add_num_denom _ _,
have hqrd : q.num * ↑(r.denom) + ↑(q.denom) * r.num ≠ 0,
  from rat.mk_num_ne_zero_of_ne_zero hqr hqreq,
begin
  conv_lhs { rw rat.num_denom q },
  rw [hqreq, padic_val_rat_le_padic_val_rat_iff p hqn hqrd hqd (mul_ne_zero hqd hrd),
    ← multiplicity_le_multiplicity_iff, mul_left_comm,
    multiplicity.mul (nat.prime_iff_prime_int.1 p_prime), add_mul],
  rw [rat.num_denom q, rat.num_denom r, padic_val_rat_le_padic_val_rat_iff p hqn hrn hqd hrd,
    ← multiplicity_le_multiplicity_iff] at h,
  calc _ ≤ min (multiplicity ↑p (q.num * ↑(r.denom) * ↑(q.denom)))
    (multiplicity ↑p (↑(q.denom) * r.num * ↑(q.denom))) : (le_min
    (by rw [@multiplicity.mul _ _ _ _ (_ * _) _ (nat.prime_iff_prime_int.1 p_prime), add_comm])
    (by rw [mul_assoc, @multiplicity.mul _ _ _ _ (q.denom : ℤ)
        (_ * _) (nat.prime_iff_prime_int.1 p_prime)];
      exact add_le_add_left' h))
    ... ≤ _ : min_le_multiplicity_add
end

theorem min_le_padic_val_rat_add {q r : ℚ}
  (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
  min (padic_val_rat p q) (padic_val_rat p r) ≤ padic_val_rat p (q + r) :=
(le_total (padic_val_rat p q) (padic_val_rat p r)).elim
  (λ h, by rw [min_eq_left h]; exact le_padic_val_rat_add_of_le _ hq hr hqr h)
  (λ h, by rw [min_eq_right h, add_comm]; exact le_padic_val_rat_add_of_le _ hr hq
    (by rwa add_comm) h)

end padic_val_rat
end padic_val_rat

def padic_norm (p : ℕ) (q : ℚ) : ℚ :=
if q = 0 then 0 else (↑p : ℚ) ^ (-(padic_val_rat p q))

namespace padic_norm

section padic_norm
open padic_val_rat
variables (p : ℕ) [hp : p.prime]
include hp

@[simp] protected lemma zero : padic_norm p 0 = 0 := by simp [padic_norm]

@[simp] protected lemma one : padic_norm p 1 = 1 := by simp [padic_norm]

@[simp] protected lemma eq_fpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
  padic_norm p q = p ^ (-(padic_val_rat p q)) :=
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
  have padic_norm p q = p ^ (-(padic_val_rat p q)), by simp [hq],
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
  unfold padic_norm,
  rw [if_neg ((@int.cast_ne_zero ℚ _ _ _ _).2 hz)],
  refine fpow_le_one_of_nonpos
    (by rw [← nat.cast_one]; exact nat.cast_le.2 (le_of_lt hp.gt_one)) _,
  rw [padic_val_rat_of_int _ hp.ne_one hz, neg_nonpos],
  exact int.coe_nat_nonneg _
end

--TODO: p implicit
private lemma nonarchimedean_aux {q r : ℚ} (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
have hnqp : padic_norm p q ≥ 0, from padic_norm.nonneg _ _,
have hnrp : padic_norm p r ≥ 0, from padic_norm.nonneg _ _,
if hq : q = 0 then
  by simp [hq, max_eq_right hnrp, le_max_right]
else if hr : r = 0 then
  by simp [hr, max_eq_left hnqp, le_max_left]
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

protected theorem image {q : ℚ} (hq : q ≠ 0) : ∃ n : ℤ, padic_norm p q = p ^ (-n) :=
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

lemma le_of_dvd {n : ℕ} {z : ℤ} (hd : ↑(p^n) ∣ z) : padic_norm p z ≤ ↑p ^ (-n : ℤ) :=
have hp' : (↑p : ℚ) ≥ 1, from show ↑p ≥ ↑(1 : ℕ), from cast_le.2 (le_of_lt hp.gt_one),
have hpn : (↑p : ℚ) ≥ 0, from le_trans zero_le_one hp',
begin
  unfold padic_norm, split_ifs with hz hz,
  { simpa [padic_norm, hz] using fpow_nonneg_of_nonneg hpn _ },
  { apply fpow_le_of_le hp',
    apply neg_le_neg,
    rw padic_val_rat_of_int _ hp.ne_one (int.cast_ne_zero.1 hz),
    apply int.coe_nat_le.2,
    rw [← enat.coe_le_coe, enat.coe_get],
    apply multiplicity.le_multiplicity_of_pow_dvd,
    { simpa using hd } }
end

end padic_norm
end padic_norm

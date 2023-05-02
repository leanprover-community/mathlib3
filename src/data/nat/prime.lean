/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/

import algebra.associated
import algebra.parity
import data.int.dvd.basic
import data.int.units
import data.nat.factorial.basic
import data.nat.gcd.basic
import data.nat.sqrt
import order.bounds.basic
import tactic.by_contra

/-!
# Prime numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

- `nat.prime`: the predicate that expresses that a natural number `p` is prime
- `nat.primes`: the subtype of natural numbers that are prime
- `nat.min_fac n`: the minimal prime factor of a natural number `n ≠ 1`
- `nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
  This also appears as `nat.not_bdd_above_set_of_prime` and `nat.infinite_set_of_prime` (the latter
  in `data.nat.prime_fin`).
- `nat.prime_iff`: `nat.prime` coincides with the general definition of `prime`
- `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime

-/

open bool subtype
open_locale nat

namespace nat

/-- `nat.prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
@[pp_nodot]
def prime (p : ℕ) := _root_.irreducible p

theorem _root_.irreducible_iff_nat_prime (a : ℕ) : irreducible a ↔ nat.prime a := iff.rfl

theorem not_prime_zero : ¬ prime 0
| h := h.ne_zero rfl

theorem not_prime_one : ¬ prime 1
| h := h.ne_one rfl

theorem prime.ne_zero {n : ℕ} (h : prime n) : n ≠ 0 := irreducible.ne_zero h

theorem prime.pos {p : ℕ} (pp : prime p) : 0 < p := nat.pos_of_ne_zero pp.ne_zero

theorem prime.two_le : ∀ {p : ℕ}, prime p → 2 ≤ p
| 0 h := (not_prime_zero h).elim
| 1 h := (not_prime_one h).elim
| (n+2) _ := le_add_self

theorem prime.one_lt {p : ℕ} : prime p → 1 < p := prime.two_le

instance prime.one_lt' (p : ℕ) [hp : _root_.fact p.prime] : _root_.fact (1 < p) := ⟨hp.1.one_lt⟩

lemma prime.ne_one {p : ℕ} (hp : p.prime) : p ≠ 1 :=
hp.one_lt.ne'

lemma prime.eq_one_or_self_of_dvd {p : ℕ} (pp : p.prime) (m : ℕ) (hm : m ∣ p) : m = 1 ∨ m = p :=
begin
  obtain ⟨n, hn⟩ := hm,
  have := pp.is_unit_or_is_unit hn,
  rw [nat.is_unit_iff, nat.is_unit_iff] at this,
  apply or.imp_right _ this,
  rintro rfl,
  rw [hn, mul_one]
end

theorem prime_def_lt'' {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m ∣ p, m = 1 ∨ m = p :=
begin
  refine ⟨λ h, ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, λ h, _⟩,
  have h1 := one_lt_two.trans_le h.1,
  refine ⟨mt nat.is_unit_iff.mp h1.ne', λ a b hab, _⟩,
  simp only [nat.is_unit_iff],
  apply or.imp_right _ (h.2 a _),
  { rintro rfl,
    rw [← mul_right_inj' (pos_of_gt h1).ne', ←hab, mul_one] },
  { rw hab,
    exact dvd_mul_right _ _ }
end

theorem prime_def_lt {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 :=
prime_def_lt''.trans $
and_congr_right $ λ p2, forall_congr $ λ m,
⟨λ h l d, (h d).resolve_right (ne_of_lt l),
 λ h d, (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left (λ l, h l d)⟩

theorem prime_def_lt' {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬ m ∣ p :=
prime_def_lt.trans $ and_congr_right $ λ p2, forall_congr $ λ m,
⟨λ h m2 l d, not_lt_of_ge m2 ((h l d).symm ▸ dec_trivial),
λ h l d, begin
  rcases m with _|_|m,
  { rw eq_zero_of_zero_dvd d at p2, revert p2, exact dec_trivial },
  { refl },
  { exact (h dec_trivial l).elim d }
end⟩

theorem prime_def_le_sqrt {p : ℕ} : prime p ↔ 2 ≤ p ∧
  ∀ m, 2 ≤ m → m ≤ sqrt p → ¬ m ∣ p :=
prime_def_lt'.trans $ and_congr_right $ λ p2,
⟨λ a m m2 l, a m m2 $ lt_of_le_of_lt l $ sqrt_lt_self p2,
 λ a, have ∀ {m k}, m ≤ k → 1 < m → p ≠ m * k, from
  λ m k mk m1 e, a m m1
    (le_sqrt.2 (e.symm ▸ nat.mul_le_mul_left m mk)) ⟨k, e⟩,
  λ m m2 l ⟨k, e⟩, begin
    cases (le_total m k) with mk km,
    { exact this mk m2 e },
    { rw [mul_comm] at e,
      refine this km (lt_of_mul_lt_mul_right _ (zero_le m)) e,
      rwa [one_mul, ← e] }
  end⟩

theorem prime_of_coprime (n : ℕ) (h1 : 1 < n) (h : ∀ m < n, m ≠ 0 → n.coprime m) : prime n :=
begin
  refine prime_def_lt.mpr ⟨h1, λ m mlt mdvd, _⟩,
  have hm : m ≠ 0,
  { rintro rfl,
    rw zero_dvd_iff at mdvd,
    exact mlt.ne' mdvd },
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd,
end

section

/--
  This instance is slower than the instance `decidable_prime` defined below,
  but has the advantage that it works in the kernel for small values.

  If you need to prove that a particular number is prime, in any case
  you should not use `dec_trivial`, but rather `by norm_num`, which is
  much faster.
  -/
local attribute [instance]
def decidable_prime_1 (p : ℕ) : decidable (prime p) :=
decidable_of_iff' _ prime_def_lt'

theorem prime_two : prime 2 := dec_trivial
theorem prime_three : prime 3 := dec_trivial

lemma prime.five_le_of_ne_two_of_ne_three {p : ℕ} (hp : p.prime) (h_two : p ≠ 2) (h_three : p ≠ 3) :
  5 ≤ p :=
begin
  by_contra' h,
  revert h_two h_three hp,
  dec_trivial!
end

end

theorem prime.pred_pos {p : ℕ} (pp : prime p) : 0 < pred p :=
lt_pred_iff.2 pp.one_lt

theorem succ_pred_prime {p : ℕ} (pp : prime p) : succ (pred p) = p :=
succ_pred_eq_of_pos pp.pos

theorem dvd_prime {p m : ℕ} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
⟨λ d, pp.eq_one_or_self_of_dvd m d, λ h, h.elim (λ e, e.symm ▸ one_dvd _) (λ e, e.symm ▸ dvd_rfl)⟩

theorem dvd_prime_two_le {p m : ℕ} (pp : prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
(dvd_prime pp).trans $ or_iff_right_of_imp $ not.elim $ ne_of_gt H

theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.prime) (qp : q.prime) : p ∣ q ↔ p = q :=
dvd_prime_two_le qp (prime.two_le pp)

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬ p ∣ 1 :=
pp.not_dvd_one

theorem not_prime_mul {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬ prime (a * b) :=
λ h, ne_of_lt (nat.mul_lt_mul_of_pos_left b1 (lt_of_succ_lt a1)) $
by simpa using (dvd_prime_two_le h a1).1 (dvd_mul_right _ _)

lemma not_prime_mul' {a b n : ℕ} (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬ prime n :=
by { rw ← h, exact not_prime_mul h₁ h₂ }

lemma prime_mul_iff {a b : ℕ} :
  nat.prime (a * b) ↔ (a.prime ∧ b = 1) ∨ (b.prime ∧ a = 1) :=
by simp only [iff_self, irreducible_mul_iff, ←irreducible_iff_nat_prime, nat.is_unit_iff]

lemma prime.dvd_iff_eq {p a : ℕ} (hp : p.prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a :=
begin
  refine ⟨_, by { rintro rfl, refl }⟩,
  -- rintro ⟨j, rfl⟩ does not work, due to `nat.prime` depending on the class `irreducible`
  rintro ⟨j, hj⟩,
  rw hj at hp ⊢,
  rcases prime_mul_iff.mp hp with ⟨h, rfl⟩ | ⟨h, rfl⟩,
  { exact mul_one _ },
  { exact (a1 rfl).elim }
end

section min_fac

lemma min_fac_lemma (n k : ℕ) (h : ¬ n < k * k) :
  sqrt n - k < sqrt n + 2 - k :=
(tsub_lt_tsub_iff_right $ le_sqrt.2 $ le_of_not_gt h).2 $
nat.lt_add_of_pos_right dec_trivial

/-- If `n < k * k`, then `min_fac_aux n k = n`, if `k | n`, then `min_fac_aux n k = k`.
  Otherwise, `min_fac_aux n k = min_fac_aux n (k+2)` using well-founded recursion.
  If `n` is odd and `1 < n`, then then `min_fac_aux n 3` is the smallest prime factor of `n`. -/
def min_fac_aux (n : ℕ) : ℕ → ℕ
| k :=
  if h : n < k * k then n else
  if k ∣ n then k else
  have _, from min_fac_lemma n k h,
  min_fac_aux (k + 2)
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def min_fac : ℕ → ℕ
| 0 := 2
| 1 := 1
| (n+2) := if 2 ∣ n then 2 else min_fac_aux (n + 2) 3

@[simp] theorem min_fac_zero : min_fac 0 = 2 := rfl
@[simp] theorem min_fac_one : min_fac 1 = 1 := rfl

theorem min_fac_eq : ∀ n, min_fac n = if 2 ∣ n then 2 else min_fac_aux n 3
| 0     := by simp
| 1     := by simp [show 2≠1, from dec_trivial]; rw min_fac_aux; refl
| (n+2) :=
  have 2 ∣ n + 2 ↔ 2 ∣ n, from
    (nat.dvd_add_iff_left (by refl)).symm,
  by simp [min_fac, this]; congr

private def min_fac_prop (n k : ℕ) :=
  2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

theorem min_fac_aux_has_prop {n : ℕ} (n2 : 2 ≤ n) :
  ∀ k i, k = 2*i+3 → (∀ m, 2 ≤ m → m ∣ n → k ≤ m) → min_fac_prop n (min_fac_aux n k)
| k := λ i e a, begin
  rw min_fac_aux,
  by_cases h : n < k*k; simp [h],
  { have pp : prime n :=
      prime_def_le_sqrt.2 ⟨n2, λ m m2 l d,
        not_lt_of_ge l $ lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩,
    from ⟨n2, dvd_rfl, λ m m2 d, le_of_eq
      ((dvd_prime_two_le pp m2).1 d).symm⟩ },
  have k2 : 2 ≤ k, { subst e, exact dec_trivial },
  by_cases dk : k ∣ n; simp [dk],
  { exact ⟨k2, dk, a⟩ },
  { refine have _, from min_fac_lemma n k h,
      min_fac_aux_has_prop (k+2) (i+1)
        (by simp [e, left_distrib]) (λ m m2 d, _),
    cases nat.eq_or_lt_of_le (a m m2 d) with me ml,
    { subst me, contradiction },
    apply (nat.eq_or_lt_of_le ml).resolve_left, intro me,
    rw [← me, e] at d, change 2 * (i + 2) ∣ n at d,
    have := a _ le_rfl (dvd_of_mul_right_dvd d),
    rw e at this, exact absurd this dec_trivial }
end
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

theorem min_fac_has_prop {n : ℕ} (n1 : n ≠ 1) :
  min_fac_prop n (min_fac n) :=
begin
  by_cases n0 : n = 0, {simp [n0, min_fac_prop, ge]},
  have n2 : 2 ≤ n, { revert n0 n1, rcases n with _|_|_; exact dec_trivial },
  simp [min_fac_eq],
  by_cases d2 : 2 ∣ n; simp [d2],
  { exact ⟨le_rfl, d2, λ k k2 d, k2⟩ },
  { refine min_fac_aux_has_prop n2 3 0 rfl
      (λ m m2 d, (nat.eq_or_lt_of_le m2).resolve_left (mt _ d2)),
    exact λ e, e.symm ▸ d }
end

theorem min_fac_dvd (n : ℕ) : min_fac n ∣ n :=
if n1 : n = 1 then by simp [n1] else (min_fac_has_prop n1).2.1

theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) :=
let ⟨f2, fd, a⟩ := min_fac_has_prop n1 in
prime_def_lt'.2 ⟨f2, λ m m2 l d, not_le_of_gt l (a m m2 (d.trans fd))⟩

theorem min_fac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → min_fac n ≤ m :=
by by_cases n1 : n = 1;
  [exact λ m m2 d, n1.symm ▸ le_trans dec_trivial m2,
    exact (min_fac_has_prop n1).2.2]

theorem min_fac_pos (n : ℕ) : 0 < min_fac n :=
by by_cases n1 : n = 1;
    [exact n1.symm ▸ dec_trivial, exact (min_fac_prime n1).pos]

theorem min_fac_le {n : ℕ} (H : 0 < n) : min_fac n ≤ n :=
le_of_dvd H (min_fac_dvd n)

theorem le_min_fac {m n : ℕ} : n = 1 ∨ m ≤ min_fac n ↔ ∀ p, prime p → p ∣ n → m ≤ p :=
⟨λ h p pp d, h.elim
  (by rintro rfl; cases pp.not_dvd_one d)
  (λ h, le_trans h $ min_fac_le_of_dvd pp.two_le d),
  λ H, or_iff_not_imp_left.2 $ λ n1, H _ (min_fac_prime n1) (min_fac_dvd _)⟩

theorem le_min_fac' {m n : ℕ} : n = 1 ∨ m ≤ min_fac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
⟨λ h p (pp:1<p) d, h.elim
  (by rintro rfl; cases not_le_of_lt pp (le_of_dvd dec_trivial d))
  (λ h, le_trans h $ min_fac_le_of_dvd pp d),
  λ H, le_min_fac.2 (λ p pp d, H p pp.two_le d)⟩

theorem prime_def_min_fac {p : ℕ} : prime p ↔ 2 ≤ p ∧ min_fac p = p :=
⟨λ pp, ⟨pp.two_le,
  let ⟨f2, fd, a⟩ := min_fac_has_prop $ ne_of_gt pp.one_lt in
  ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
  λ ⟨p2, e⟩, e ▸ min_fac_prime (ne_of_gt p2)⟩

@[simp] lemma prime.min_fac_eq {p : ℕ} (hp : prime p) : min_fac p = p :=
(prime_def_min_fac.1 hp).2

/--
This instance is faster in the virtual machine than `decidable_prime_1`,
but slower in the kernel.

If you need to prove that a particular number is prime, in any case
you should not use `dec_trivial`, but rather `by norm_num`, which is
much faster.
-/
instance decidable_prime (p : ℕ) : decidable (prime p) :=
decidable_of_iff' _ prime_def_min_fac

theorem not_prime_iff_min_fac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬ prime n ↔ min_fac n < n :=
(not_congr $ prime_def_min_fac.trans $ and_iff_right n2).trans $
  (lt_iff_le_and_ne.trans $ and_iff_right $ min_fac_le $ le_of_succ_le n2).symm

lemma min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬ prime n) : min_fac n ≤ n / min_fac n :=
match min_fac_dvd n with
| ⟨0, h0⟩     := absurd pos $ by rw [h0, mul_zero]; exact dec_trivial
| ⟨1, h1⟩     :=
  begin
    rw mul_one at h1,
    rw [prime_def_min_fac, not_and_distrib, ← h1, eq_self_iff_true, not_true, or_false,
      not_le] at np,
    rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), min_fac_one, nat.div_one]
  end
| ⟨(x+2), hx⟩ :=
  begin
    conv_rhs { congr, rw hx },
    rw [nat.mul_div_cancel_left _ (min_fac_pos _)],
    exact min_fac_le_of_dvd dec_trivial ⟨min_fac n, by rwa mul_comm⟩
  end
end

/--
The square of the smallest prime factor of a composite number `n` is at most `n`.
-/
lemma min_fac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬ prime n) : (min_fac n)^2 ≤ n :=
have t : (min_fac n) ≤ (n/min_fac n) := min_fac_le_div w h,
calc
(min_fac n)^2 = (min_fac n) * (min_fac n)   : sq (min_fac n)
          ... ≤ (n/min_fac n) * (min_fac n) : nat.mul_le_mul_right (min_fac n) t
          ... ≤ n                           : div_mul_le_self n (min_fac n)

@[simp]
lemma min_fac_eq_one_iff {n : ℕ} : min_fac n = 1 ↔ n = 1 :=
begin
  split,
  { intro h,
    by_contradiction hn,
    have := min_fac_prime hn,
    rw h at this,
    exact not_prime_one this, },
  { rintro rfl, refl, }
end

@[simp]
lemma min_fac_eq_two_iff (n : ℕ) : min_fac n = 2 ↔ 2 ∣ n :=
begin
  split,
  { intro h,
    convert min_fac_dvd _,
    rw h, },
  { intro h,
    have ub := min_fac_le_of_dvd (le_refl 2) h,
    have lb := min_fac_pos n,
    apply ub.eq_or_lt.resolve_right (λ h', _),
    have := le_antisymm (nat.succ_le_of_lt lb) (lt_succ_iff.mp h'),
    rw [eq_comm, nat.min_fac_eq_one_iff] at this,
    subst this,
    exact not_lt_of_le (le_of_dvd zero_lt_one h) one_lt_two }
end

end min_fac

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬ prime n) :
  ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
⟨min_fac n, min_fac_dvd _, ne_of_gt (min_fac_prime (ne_of_gt n2)).one_lt,
  ne_of_lt $ (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬ prime n) :
  ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
⟨min_fac n, min_fac_dvd _, (min_fac_prime (ne_of_gt n2)).two_le,
  (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, prime p ∧ p ∣ n :=
⟨min_fac n, min_fac_prime hn, min_fac_dvd _⟩

theorem dvd_of_forall_prime_mul_dvd {a b : ℕ}
  (hdvd : ∀ p : ℕ, p.prime → p ∣ a → p * a ∣ b) : a ∣ b :=
begin
  obtain rfl | ha := eq_or_ne a 1, { apply one_dvd },
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha,
  exact trans (dvd_mul_left a p) (hdvd p hp.1 hp.2),
end

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
let p := min_fac (n! + 1) in
have f1 : n! + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ factorial_pos _,
have pp : prime p, from min_fac_prime f1,
have np : n ≤ p, from le_of_not_ge $ λ h,
  have h₁ : p ∣ n!, from dvd_factorial (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  pp.not_dvd_one h₂,
⟨p, np, pp⟩

/-- A version of `nat.exists_infinite_primes` using the `bdd_above` predicate. -/
lemma not_bdd_above_set_of_prime : ¬ bdd_above {p | prime p} :=
begin
  rw not_bdd_above_iff,
  intro n,
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ,
  exact ⟨p, hp, hi⟩,
end

lemma prime.eq_two_or_odd {p : ℕ} (hp : prime p) : p = 2 ∨ p % 2 = 1 :=
p.mod_two_eq_zero_or_one.imp_left
  (λ h, ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left dec_trivial).symm)

lemma prime.eq_two_or_odd' {p : ℕ} (hp : prime p) : p = 2 ∨ odd p :=
or.imp_right (λ h, ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

lemma prime.even_iff {p : ℕ} (hp : prime p) : even p ↔ p = 2 :=
by rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]

lemma prime.odd_of_ne_two {p : ℕ} (hp : p.prime) (h_two : p ≠ 2) : odd p :=
hp.eq_two_or_odd'.resolve_left h_two

lemma prime.even_sub_one {p : ℕ} (hp : p.prime) (h2 : p ≠ 2) : even (p - 1) :=
let ⟨n, hn⟩ := hp.odd_of_ne_two h2 in ⟨n, by rw [hn, nat.add_sub_cancel, two_mul]⟩

/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`. -/
lemma prime.mod_two_eq_one_iff_ne_two {p : ℕ} [fact p.prime] : p % 2 = 1 ↔ p ≠ 2 :=
begin
  refine ⟨λ h hf, _, (nat.prime.eq_two_or_odd $ fact.out p.prime).resolve_left⟩,
  rw hf at h,
  simpa using h,
end

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, prime k → k ∣ m → ¬ k ∣ n) : coprime m n :=
begin
  rw [coprime_iff_gcd_eq_one],
  by_contra g2,
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2,
  apply H p hp; apply dvd_trans hpdvd,
  { exact gcd_dvd_left _ _ },
  { exact gcd_dvd_right _ _ }
end

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, prime k → k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
coprime_of_dvd $ λk kp km kn, not_le_of_gt kp.one_lt $ le_of_dvd zero_lt_one $ H k kp km kn

theorem factors_lemma {k} : (k+2) / min_fac (k+2) < k+2 :=
div_lt_self dec_trivial (min_fac_prime dec_trivial).one_lt

theorem prime.coprime_iff_not_dvd {p n : ℕ} (pp : prime p) : coprime p n ↔ ¬ p ∣ n :=
⟨λ co d, pp.not_dvd_one $ co.dvd_of_dvd_mul_left (by simp [d]),
 λ nd, coprime_of_dvd $ λ m m2 mp, ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

theorem prime.dvd_iff_not_coprime {p n : ℕ} (pp : prime p) : p ∣ n ↔ ¬ coprime p n :=
iff_not_comm.2 pp.coprime_iff_not_dvd

theorem prime.not_coprime_iff_dvd {m n : ℕ} :
  ¬ coprime m n ↔ ∃p, prime p ∧ p ∣ m ∧ p ∣ n :=
begin
  apply iff.intro,
  { intro h,
    exact ⟨min_fac (gcd m n), min_fac_prime h,
      ((min_fac_dvd (gcd m n)).trans (gcd_dvd_left m n)),
      ((min_fac_dvd (gcd m n)).trans (gcd_dvd_right m n))⟩ },
  { intro h,
    cases h with p hp,
    apply nat.not_coprime_of_dvd_of_dvd (prime.one_lt hp.1) hp.2.1 hp.2.2 }
end

theorem prime.dvd_mul {p m n : ℕ} (pp : prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
⟨λ H, or_iff_not_imp_left.2 $ λ h,
  (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
 or.rec (λ h : p ∣ m, h.mul_right _) (λ h : p ∣ n, h.mul_left _)⟩

theorem prime.not_dvd_mul {p m n : ℕ} (pp : prime p)
  (Hm : ¬ p ∣ m) (Hn : ¬ p ∣ n) : ¬ p ∣ m * n :=
mt pp.dvd_mul.1 $ by simp [Hm, Hn]

theorem prime_iff {p : ℕ} : p.prime ↔ _root_.prime p :=
⟨λ h, ⟨h.ne_zero, h.not_unit, λ a b, h.dvd_mul.mp⟩, prime.irreducible⟩

alias prime_iff ↔ prime.prime _root_.prime.nat_prime
attribute [protected, nolint dup_namespace] prime.prime

theorem irreducible_iff_prime {p : ℕ} : irreducible p ↔ _root_.prime p := prime_iff

theorem prime.dvd_of_dvd_pow {p m n : ℕ} (pp : prime p) (h : p ∣ m^n) : p ∣ m :=
begin
  induction n with n IH,
  { exact pp.not_dvd_one.elim h },
  { rw pow_succ at h, exact (pp.dvd_mul.1 h).elim id IH }
end

lemma prime.pow_not_prime {x n : ℕ} (hn : 2 ≤ n) : ¬ (x ^ n).prime :=
λ hp, (hp.eq_one_or_self_of_dvd x $ dvd_trans ⟨x, sq _⟩ (pow_dvd_pow _ hn)).elim
  (λ hx1, hp.ne_one $ hx1.symm ▸ one_pow _)
  (λ hxn, lt_irrefl x $ calc x = x ^ 1 : (pow_one _).symm
     ... < x ^ n : nat.pow_right_strict_mono (hxn.symm ▸ hp.two_le) hn
     ... = x : hxn.symm)

lemma prime.pow_not_prime' {x : ℕ} : ∀ {n : ℕ}, n ≠ 1 → ¬ (x ^ n).prime
| 0     := λ _, not_prime_one
| 1     := λ h, (h rfl).elim
| (n+2) := λ _, prime.pow_not_prime le_add_self

lemma prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).prime) : n = 1 :=
not_imp_not.mp prime.pow_not_prime' h

lemma prime.pow_eq_iff {p a k : ℕ} (hp : p.prime) : a ^ k = p ↔ a = p ∧ k = 1 :=
begin
  refine ⟨λ h, _, λ h, by rw [h.1, h.2, pow_one]⟩,
  rw ←h at hp,
  rw [←h, hp.eq_one_of_pow, eq_self_iff_true, and_true, pow_one],
end

lemma pow_min_fac {n k : ℕ} (hk : k ≠ 0) : (n^k).min_fac = n.min_fac :=
begin
  rcases eq_or_ne n 1 with rfl | hn,
  { simp },
  have hnk : n ^ k ≠ 1 := λ hk', hn ((pow_eq_one_iff hk).1 hk'),
  apply (min_fac_le_of_dvd (min_fac_prime hn).two_le ((min_fac_dvd n).pow hk)).antisymm,
  apply min_fac_le_of_dvd (min_fac_prime hnk).two_le
    ((min_fac_prime hnk).dvd_of_dvd_pow (min_fac_dvd _)),
end

lemma prime.pow_min_fac {p k : ℕ} (hp : p.prime) (hk : k ≠ 0) : (p^k).min_fac = p :=
by rw [pow_min_fac hk, hp.min_fac_eq]

lemma prime.mul_eq_prime_sq_iff {x y p : ℕ} (hp : p.prime) (hx : x ≠ 1) (hy : y ≠ 1) :
  x * y = p ^ 2 ↔ x = p ∧ y = p :=
⟨λ h, have pdvdxy : p ∣ x * y, by rw h; simp [sq],
begin
  -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
  suffices : ∀ (x' y' : ℕ), x' ≠ 1 → y' ≠ 1 → x' * y' = p ^ 2 → p ∣ x' → x' = p ∧ y' = p,
  { obtain hx|hy := hp.dvd_mul.1 pdvdxy;
      [skip, rw and_comm];
      [skip, rw mul_comm at h pdvdxy];
      apply this;
      assumption },
  clear_dependent x y,
  rintros x y hx hy h ⟨a, ha⟩,
  have hap : a ∣ p, from ⟨y, by rwa [ha, sq,
        mul_assoc, mul_right_inj' hp.ne_zero, eq_comm] at h⟩,
  exact ((nat.dvd_prime hp).1 hap).elim
    (λ _, by clear_aux_decl; simp [*, sq, mul_right_inj' hp.ne_zero] at *
      {contextual := tt})
    (λ _, by clear_aux_decl; simp [*, sq, mul_comm, mul_assoc,
      mul_right_inj' hp.ne_zero, nat.mul_right_eq_self_iff hp.pos] at *
      {contextual := tt})
end,
λ ⟨h₁, h₂⟩, h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩

lemma prime.dvd_factorial : ∀ {n p : ℕ} (hp : prime p), p ∣ n! ↔ p ≤ n
| 0 p hp := iff_of_false hp.not_dvd_one (not_le_of_lt hp.pos)
| (n+1) p hp := begin
  rw [factorial_succ, hp.dvd_mul, prime.dvd_factorial hp],
  exact ⟨λ h, h.elim (le_of_dvd (succ_pos _)) le_succ_of_le,
    λ h, (_root_.lt_or_eq_of_le h).elim (or.inr ∘ le_of_lt_succ)
      (λ h, or.inl $ by rw h)⟩
end

theorem prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : prime p) (h : ¬ p ∣ a) : coprime a (p^m) :=
(pp.coprime_iff_not_dvd.2 h).symm.pow_right _

theorem coprime_primes {p q : ℕ} (pp : prime p) (pq : prime q) : coprime p q ↔ p ≠ q :=
pp.coprime_iff_not_dvd.trans $ not_congr $ dvd_prime_two_le pq pp.two_le

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : prime p) (pq : prime q) (h : p ≠ q) :
  coprime (p^n) (q^m) :=
((coprime_primes pp pq).2 h).pow _ _

theorem coprime_or_dvd_of_prime {p} (pp : prime p) (i : ℕ) : coprime p i ∨ p ∣ i :=
by rw [pp.dvd_iff_not_coprime]; apply em

lemma coprime_of_lt_prime {n p} (n_pos : 0 < n) (hlt : n < p) (pp : prime p) :
  coprime p n :=
(coprime_or_dvd_of_prime pp n).resolve_right $ λ h, lt_le_antisymm hlt (le_of_dvd n_pos h)

lemma eq_or_coprime_of_le_prime {n p} (n_pos : 0 < n) (hle : n ≤ p) (pp : prime p) :
  p = n ∨ coprime p n :=
hle.eq_or_lt.imp eq.symm (λ h, coprime_of_lt_prime n_pos h pp)

theorem dvd_prime_pow {p : ℕ} (pp : prime p) {m i : ℕ} : i ∣ (p^m) ↔ ∃ k ≤ m, i = p^k :=
by simp_rw [dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]

lemma prime.dvd_mul_of_dvd_ne {p1 p2 n : ℕ} (h_neq : p1 ≠ p2) (pp1 : prime p1) (pp2 : prime p2)
  (h1 : p1 ∣ n) (h2 : p2 ∣ n) : (p1 * p2 ∣ n) :=
coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_neq) h1 h2

/--
If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
lemma eq_prime_pow_of_dvd_least_prime_pow
  {a p k : ℕ} (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) :
  a = p^(k+1) :=
begin
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂,
  congr,
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (prime.one_lt pp))).1 h₁)),
end

lemma ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.prime ∧ p ∣ n
| 0 := by simpa using (Exists.intro 2 nat.prime_two)
| 1 := by simp [nat.not_prime_one]
| (n+2) :=
let a := n+2 in
let ha : a ≠ 1 := nat.succ_succ_ne_one n in
begin
  simp only [true_iff, ne.def, not_false_iff, ha],
  exact ⟨a.min_fac, nat.min_fac_prime ha, a.min_fac_dvd⟩,
end

lemma eq_one_iff_not_exists_prime_dvd {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.prime → ¬p ∣ n :=
by simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : prime p) {m n k l : ℕ}
      (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k+l+1) ∣ m*n) :
      p ^ (k+1) ∣ m ∨ p ^ (l+1) ∣ n :=
have hpd : p^(k+l)*p ∣ m*n, by rwa pow_succ' at hpmn,
have hpd2 : p ∣ (m*n) / p ^ (k+l), from dvd_div_of_mul_dvd hpd,
have hpd3 : p ∣ (m*n) / (p^k * p^l), by simpa [pow_add] using hpd2,
have hpd4 : p ∣ (m / p^k) * (n / p^l), by simpa [nat.div_mul_div_comm hpm hpn] using hpd3,
have hpd5 : p ∣ (m / p^k) ∨ p ∣ (n / p^l), from (prime.dvd_mul p_prime).1 hpd4,
suffices p^k*p ∣ m ∨ p^l*p ∣ n, by rwa [pow_succ', pow_succ'],
  hpd5.elim
    (assume : p ∣ m / p ^ k, or.inl $ mul_dvd_of_dvd_div hpm this)
    (assume : p ∣ n / p ^ l, or.inr $ mul_dvd_of_dvd_div hpn this)

lemma prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
⟨λ hp, ⟨int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt int.is_unit_iff_nat_abs_eq.1 hp.ne_one,
  λ a b h, by rw [← int.dvd_nat_abs, int.coe_nat_dvd, int.nat_abs_mul, hp.dvd_mul] at h;
    rwa [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd]⟩,
  λ hp, nat.prime_iff.2 ⟨int.coe_nat_ne_zero.1 hp.1,
      mt nat.is_unit_iff.1 $ λ h, by simpa [h, not_prime_one] using hp,
    λ a b, by simpa only [int.coe_nat_dvd, (int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- The type of prime numbers -/
def primes := {p : ℕ // p.prime}

namespace primes

instance : has_repr nat.primes := ⟨λ p, repr p.val⟩
instance inhabited_primes : inhabited primes := ⟨⟨2, prime_two⟩⟩

instance coe_nat : has_coe nat.primes ℕ := ⟨subtype.val⟩

theorem coe_nat_injective : function.injective (coe : nat.primes → ℕ) :=
subtype.coe_injective

theorem coe_nat_inj (p q : nat.primes) : (p : ℕ) = (q : ℕ) ↔ p = q :=
subtype.ext_iff.symm

end primes

instance monoid.prime_pow {α : Type*} [monoid α] : has_pow α primes := ⟨λ x p, x^(p : ℕ)⟩

end nat

namespace nat

instance fact_prime_two : fact (prime 2) := ⟨prime_two⟩

instance fact_prime_three : fact (prime 3) := ⟨prime_three⟩

end nat

namespace int
lemma prime_two : prime (2 : ℤ) := nat.prime_iff_prime_int.mp nat.prime_two
lemma prime_three : prime (3 : ℤ) := nat.prime_iff_prime_int.mp nat.prime_three
end int

assert_not_exists multiset

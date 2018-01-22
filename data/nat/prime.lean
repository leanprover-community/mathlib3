/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

Prime numbers.
-/
import data.nat.sqrt data.nat.gcd
open bool subtype

namespace nat
open decidable

/-- `prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
def prime (p : ℕ) := p ≥ 2 ∧ ∀ m ∣ p, m = 1 ∨ m = p

theorem prime.ge_two {p : ℕ} : prime p → p ≥ 2 := and.left

theorem prime.gt_one {p : ℕ} : prime p → p > 1 := prime.ge_two

theorem prime_def_lt {p : ℕ} : prime p ↔ p ≥ 2 ∧ ∀ m < p, m ∣ p → m = 1 :=
and_congr_right $ λ p2, forall_congr $ λ m,
⟨λ h l d, (h d).resolve_right (ne_of_lt l),
 λ h d, (lt_or_eq_of_le $
   le_of_dvd (le_of_succ_le p2) d).imp_left (λ l, h l d)⟩

theorem prime_def_lt' {p : ℕ} : prime p ↔ p ≥ 2 ∧ ∀ m, 2 ≤ m → m < p → ¬ m ∣ p :=
prime_def_lt.trans $ and_congr_right $ λ p2, forall_congr $ λ m,
⟨λ h m2 l d, not_lt_of_ge m2 ((h l d).symm ▸ dec_trivial),
λ h l d, begin
  rcases m with _|_|m,
  { rw eq_zero_of_zero_dvd d at p2, revert p2, exact dec_trivial },
  { refl },
  { exact (h dec_trivial l).elim d }
end⟩

theorem prime_def_le_sqrt {p : ℕ} : prime p ↔ p ≥ 2 ∧
  ∀ m, 2 ≤ m → m ≤ sqrt p → ¬ m ∣ p :=
prime_def_lt'.trans $ and_congr_right $ λ p2,
⟨λ a m m2 l, a m m2 $ lt_of_le_of_lt l $ sqrt_lt_self p2,
 λ a, have ∀ {m k}, m ≤ k → 1 < m → p ≠ m * k, from
  λ m k mk m1 e, a m m1
    (le_sqrt.2 (e.symm ▸ mul_le_mul_left m mk)) ⟨k, e⟩,
  λ m m2 l ⟨k, e⟩, begin
    cases (le_total m k) with mk km,
    { exact this mk m2 e },
    { rw [mul_comm] at e,
      refine this km (lt_of_mul_lt_mul_right _ (zero_le m)) e,
      rwa [one_mul, ← e] }
  end⟩

def decidable_prime_1 (p : ℕ) : decidable (prime p) :=
decidable_of_iff' _ prime_def_lt'
local attribute [instance] decidable_prime_1

theorem prime.pos {p : ℕ} (pp : prime p) : p > 0 :=
lt_of_succ_lt pp.gt_one

theorem not_prime_zero : ¬ prime 0 := dec_trivial

theorem not_prime_one : ¬ prime 1 := dec_trivial

theorem prime_two : prime 2 := dec_trivial

theorem prime_three : prime 3 := dec_trivial

theorem prime.pred_pos {p : ℕ} (pp : prime p) : pred p > 0 :=
lt_pred_of_succ_lt pp.gt_one

theorem succ_pred_prime {p : ℕ} (pp : prime p) : succ (pred p) = p :=
succ_pred_eq_of_pos pp.pos

theorem dvd_prime {p m : ℕ} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
⟨λ d, pp.2 m d, λ h, h.elim (λ e, e.symm ▸ one_dvd _) (λ e, e.symm ▸ dvd_refl _)⟩

theorem dvd_prime_ge_two {p m : ℕ} (pp : prime p) (H : m ≥ 2) : m ∣ p ↔ m = p :=
(dvd_prime pp).trans $ or_iff_right_of_imp $ not.elim $ ne_of_gt H

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬ p ∣ 1
| d := (not_le_of_gt pp.gt_one) $ le_of_dvd dec_trivial d

section min_fac
  private lemma min_fac_lemma (n k : ℕ) (h : ¬ k * k > n) :
    sqrt n - k < sqrt n + 2 - k :=
  (nat.sub_lt_sub_right_iff $ le_sqrt.2 $ le_of_not_gt h).2 $
  nat.lt_add_of_pos_right dec_trivial

  def min_fac_aux (n : ℕ) : ℕ → ℕ | k :=
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

  theorem min_fac_eq : ∀ {n : ℕ} (n2 : n ≥ 2),
    min_fac n = if 2 ∣ n then 2 else min_fac_aux n 3
  | 1     h := (dec_trivial : ¬ _).elim h
  | (n+2) h := by by_cases 2 ∣ n;
    simp [min_fac, (nat.dvd_add_iff_left (dvd_refl 2)).symm, h]

  private def min_fac_prop (n k : ℕ) :=
    k ≥ 2 ∧ k ∣ n ∧ ∀ m ≥ 2, m ∣ n → k ≤ m

  theorem min_fac_aux_has_prop {n : ℕ} (n2 : n ≥ 2) (nd2 : ¬ 2 ∣ n) :
    ∀ k i, k = 2*i+3 → (∀ m ≥ 2, m ∣ n → k ≤ m) → min_fac_prop n (min_fac_aux n k)
  | k := λ i e a, begin
    rw min_fac_aux,
    by_cases h : n < k*k; simp [h],
    { have pp : prime n :=
        prime_def_le_sqrt.2 ⟨n2, λ m m2 l d,
          not_lt_of_ge l $ lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩,
      from ⟨n2, dvd_refl _, λ m m2 d, le_of_eq
        ((dvd_prime_ge_two pp m2).1 d).symm⟩ },
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
      have := dvd_of_mul_right_dvd d, contradiction }
  end
  using_well_founded {rel_tac :=
    λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

  theorem min_fac_has_prop {n : ℕ} (n1 : n ≠ 1) :
    min_fac_prop n (min_fac n) :=
  begin
    by_cases n0 : n = 0, {simp [n0, min_fac_prop, ge]},
    have n2 : 2 ≤ n, { revert n0 n1, rcases n with _|_|_; exact dec_trivial },
    simp [min_fac_eq n2],
    by_cases d2 : 2 ∣ n; simp [d2],
    { exact ⟨le_refl _, d2, λ k k2 d, k2⟩ },
    { refine min_fac_aux_has_prop n2 d2 3 0 rfl
        (λ m m2 d, (nat.eq_or_lt_of_le m2).resolve_left (mt _ d2)),
      exact λ e, e.symm ▸ d }
  end

  theorem min_fac_dvd (n : ℕ) : min_fac n ∣ n :=
  by by_cases n1 : n = 1;
     [exact n1.symm ▸ dec_trivial, exact (min_fac_has_prop n1).2.1]

  theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) :=
  let ⟨f2, fd, a⟩ := min_fac_has_prop n1 in
  prime_def_lt'.2 ⟨f2, λ m m2 l d, not_le_of_gt l (a m m2 (dvd_trans d fd))⟩

  theorem min_fac_le_of_dvd (n : ℕ) : ∀ (m : ℕ), m ≥ 2 → m ∣ n → min_fac n ≤ m :=
  by by_cases n1 : n = 1;
    [exact λ m m2 d, n1.symm ▸ le_trans dec_trivial m2,
     exact (min_fac_has_prop n1).2.2]

  theorem min_fac_pos (n : ℕ) : min_fac n > 0 :=
  by by_cases n1 : n = 1;
     [exact n1.symm ▸ dec_trivial, exact (min_fac_prime n1).pos]

  theorem min_fac_le {n : ℕ} (H : n > 0) : min_fac n ≤ n :=
  le_of_dvd H (min_fac_dvd n)

  theorem prime_def_min_fac {p : ℕ} : prime p ↔ p ≥ 2 ∧ min_fac p = p :=
  ⟨λ pp, ⟨pp.ge_two,
    let ⟨f2, fd, a⟩ := min_fac_has_prop $ ne_of_gt pp.gt_one in
    ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
   λ ⟨p2, e⟩, e ▸ min_fac_prime (ne_of_gt p2)⟩

  instance decidable_prime (p : ℕ) : decidable (prime p) :=
  decidable_of_iff' _ prime_def_min_fac

  theorem not_prime_iff_min_fac_lt {n : ℕ} (n2 : n ≥ 2) : ¬ prime n ↔ min_fac n < n :=
  (not_congr $ prime_def_min_fac.trans $ and_iff_right n2).trans $
    (lt_iff_le_and_ne.trans $ and_iff_right $ min_fac_le $ le_of_succ_le n2).symm

end min_fac

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : n ≥ 2) (np : ¬ prime n) :
  ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
⟨min_fac n, min_fac_dvd _, ne_of_gt (min_fac_prime (ne_of_gt n2)).gt_one,
  ne_of_lt $ (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : n ≥ 2) (np : ¬ prime n) :
  ∃ m, m ∣ n ∧ m ≥ 2 ∧ m < n :=
⟨min_fac n, min_fac_dvd _, (min_fac_prime (ne_of_gt n2)).ge_two,
  (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_prime_and_dvd {n : ℕ} (n2 : n ≥ 2) : ∃ p, prime p ∧ p ∣ n :=
⟨min_fac n, min_fac_prime (ne_of_gt n2), min_fac_dvd _⟩

theorem exists_infinite_primes : ∀ n : ℕ, ∃ p, p ≥ n ∧ prime p :=
suffices ∀ {n}, n ≥ 2 → ∃ p, p ≥ n ∧ prime p, from
λ n, let ⟨p, h, pp⟩ := this (nat.le_add_left 2 n) in
  ⟨p, le_trans (nat.le_add_right n 2) h, pp⟩,
λ n n2,
  let p := min_fac (fact n + 1) in
  have f1 : fact n + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ fact_pos _,
  have pp : prime p, from min_fac_prime f1,
  have n ≤ p, from le_of_not_ge $ λ h,
    have p ∣ fact n, from dvd_fact (min_fac_pos _) h,
    have p ∣ 1, from (nat.dvd_add_iff_right this).2 (min_fac_dvd _),
    pp.not_dvd_one this,
  ⟨p, this, pp⟩

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → list ℕ
| 0 := []
| 1 := []
| n@(k+2) := let m := min_fac n in
  have n / m < n, from
    have n * 1 < n * min_fac n, from nat.mul_lt_mul_of_pos_left
      (min_fac_prime dec_trivial).gt_one (succ_pos _),
    (nat.div_lt_iff_lt_mul _ _ (min_fac_pos _)).2 $ by simpa,
  m :: factors (n / m)

theorem prime.coprime_iff_not_dvd {p n : ℕ} (pp : prime p) : coprime p n ↔ ¬ p ∣ n :=
⟨λ co d, pp.not_dvd_one $ co.dvd_of_dvd_mul_left (by simp [d]),
 λ nd, coprime_of_dvd $ λ m m2 mp, ((dvd_prime_ge_two pp m2).1 mp).symm ▸ nd⟩

theorem prime.dvd_iff_not_coprime {p n : ℕ} (pp : prime p) : p ∣ n ↔ ¬ coprime p n :=
iff_not_comm.2 pp.coprime_iff_not_dvd

theorem prime.dvd_mul {p m n : ℕ} (pp : prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
⟨λ H, or_iff_not_imp_left.2 $ λ h,
  (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
 or.rec (λ h, dvd_mul_of_dvd_left h _) (λ h, dvd_mul_of_dvd_right h _)⟩

theorem prime.not_dvd_mul {p m n : ℕ} (pp : prime p)
  (Hm : ¬ p ∣ m) (Hn : ¬ p ∣ n) : ¬ p ∣ m * n :=
mt pp.dvd_mul.1 $ by simp [Hm, Hn]

theorem prime.dvd_of_dvd_pow {p m n : ℕ} (pp : prime p) (h : p ∣ m^n) : p ∣ m :=
by induction n with n IH;
   [exact pp.not_dvd_one.elim h,
    exact (pp.dvd_mul.1 h).elim IH id]

theorem prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : prime p) (h : ¬ p ∣ a) : coprime a (p^m) :=
(pp.coprime_iff_not_dvd.2 h).symm.pow_right _

theorem coprime_primes {p q : ℕ} (pp : prime p) (pq : prime q) : coprime p q ↔ p ≠ q :=
pp.coprime_iff_not_dvd.trans $ not_congr $ dvd_prime_ge_two pq pp.ge_two

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : prime p) (pq : prime q) (h : p ≠ q) :
  coprime (p^n) (q^m) :=
((coprime_primes pp pq).2 h).pow _ _

theorem coprime_or_dvd_of_prime {p} (pp : prime p) (i : ℕ) : coprime p i ∨ p ∣ i :=
by rw [pp.dvd_iff_not_coprime]; apply em

theorem dvd_prime_pow {p : ℕ} (pp : prime p) {m i : ℕ} : i ∣ (p^m) ↔ ∃ k ≤ m, i = p^k :=
begin
  induction m with m IH generalizing i, {simp [pow_succ, le_zero_iff] at *},
  by_cases p ∣ i,
  { cases h with a e, subst e,
    rw [pow_succ, mul_comm (p^m) p, nat.mul_dvd_mul_iff_left pp.pos, IH],
    split; intro h; rcases h with ⟨k, h, e⟩,
    { exact ⟨succ k, succ_le_succ h, by rw [mul_comm, e]; refl⟩ },
    cases k with k,
    { apply pp.not_dvd_one.elim,
      simp at e, rw ← e, apply dvd_mul_right },
    { refine ⟨k, le_of_succ_le_succ h, _⟩,
      rwa [mul_comm, pow_succ, nat.mul_right_inj pp.pos] at e } },
  { split; intro d,
    { rw (pp.coprime_pow_of_not_dvd h).eq_one_of_dvd d,
      exact ⟨0, zero_le _, rfl⟩ },
    { rcases d with ⟨k, l, e⟩,
      rw e, exact pow_dvd_pow _ l } }
end

end nat

/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

Prime numbers.
-/
import data.nat.sqrt data.nat.gcd data.list.basic data.list.perm
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
 λ h d, (decidable.lt_or_eq_of_le $
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

lemma prime.ne_zero {n : ℕ} (h : prime n) : n ≠ 0 :=
assume hn : n = 0,
have h2 : ¬ prime 0, from dec_trivial,
h2 (hn ▸ h)

theorem prime.pos {p : ℕ} (pp : prime p) : p > 0 :=
lt_of_succ_lt pp.gt_one

theorem not_prime_zero : ¬ prime 0 := dec_trivial

theorem not_prime_one : ¬ prime 1 := dec_trivial

theorem prime_two : prime 2 := dec_trivial

theorem prime_three : prime 3 := dec_trivial

theorem prime.pred_pos {p : ℕ} (pp : prime p) : pred p > 0 :=
lt_pred_iff.2 pp.gt_one

theorem succ_pred_prime {p : ℕ} (pp : prime p) : succ (pred p) = p :=
succ_pred_eq_of_pos pp.pos

theorem dvd_prime {p m : ℕ} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
⟨λ d, pp.2 m d, λ h, h.elim (λ e, e.symm ▸ one_dvd _) (λ e, e.symm ▸ dvd_refl _)⟩

theorem dvd_prime_ge_two {p m : ℕ} (pp : prime p) (H : m ≥ 2) : m ∣ p ↔ m = p :=
(dvd_prime pp).trans $ or_iff_right_of_imp $ not.elim $ ne_of_gt H

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬ p ∣ 1
| d := (not_le_of_gt pp.gt_one) $ le_of_dvd dec_trivial d

theorem not_prime_mul {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬ prime (a * b) :=
λ h, ne_of_lt (nat.mul_lt_mul_of_pos_left b1 (lt_of_succ_lt a1)) $
by simpa using (dvd_prime_ge_two h a1).1 (dvd_mul_right _ _)

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

  theorem min_fac_eq : ∀ n, min_fac n = if 2 ∣ n then 2 else min_fac_aux n 3
  | 0     := rfl
  | 1     := by simp [show 2≠1, from dec_trivial]; rw min_fac_aux; refl
  | (n+2) :=
    have 2 ∣ n + 2 ↔ 2 ∣ n, from
      (nat.dvd_add_iff_left (by refl)).symm,
    by simp [min_fac, this]; congr

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
    simp [min_fac_eq],
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

  theorem min_fac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, m ≥ 2 → m ∣ n → min_fac n ≤ m :=
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

theorem exists_infinite_primes (n : ℕ) : ∃ p, p ≥ n ∧ prime p :=
let p := min_fac (fact n + 1) in
have f1 : fact n + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ fact_pos _,
have pp : prime p, from min_fac_prime f1,
have np : n ≤ p, from le_of_not_ge $ λ h,
  have h₁ : p ∣ fact n, from dvd_fact (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  pp.not_dvd_one h₂,
⟨p, np, pp⟩

lemma prime.eq_two_or_odd {p : ℕ} (hp : prime p) : p = 2 ∨ p % 2 = 1 :=
(nat.mod_two_eq_zero_or_one p).elim
  (λ h, or.inl ((hp.2 2 (dvd_of_mod_eq_zero h)).resolve_left dec_trivial).symm)
  or.inr

theorem factors_lemma {k} : (k+2) / min_fac (k+2) < k+2 :=
div_lt_self dec_trivial (min_fac_prime dec_trivial).gt_one

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → list ℕ
| 0 := []
| 1 := []
| n@(k+2) :=
  let m := min_fac n in have n / m < n := factors_lemma,
  m :: factors (n / m)

lemma mem_factors : ∀ {n p}, p ∈ factors n → prime p
| 0       := λ p, false.elim
| 1       := λ p, false.elim
| n@(k+2) := λ p h,
  let m := min_fac n in have n / m < n := factors_lemma,
  have h₁ : p = m ∨ p ∈ (factors (n / m)) :=
    (list.mem_cons_iff _ _ _).1 h,
  or.cases_on h₁ (λ h₂, h₂.symm ▸ min_fac_prime dec_trivial)
    mem_factors

lemma prod_factors : ∀ {n}, 0 < n → list.prod (factors n) = n
| 0       := (lt_irrefl _).elim
| 1       := λ h, rfl
| n@(k+2) := λ h,
  let m := min_fac n in have n / m < n := factors_lemma,
  show list.prod (m :: factors (n / m)) = n, from
  have h₁ : 0 < n / m :=
    nat.pos_of_ne_zero $ λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [list.prod_cons, prod_factors h₁, nat.mul_div_cancel' (min_fac_dvd _)]

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

lemma prime.dvd_fact : ∀ {n p : ℕ} (hp : prime p), p ∣ n.fact ↔ p ≤ n
| 0 p hp := iff_of_false hp.not_dvd_one (not_le_of_lt hp.pos)
| (n+1) p hp := begin
  rw [fact_succ, hp.dvd_mul, prime.dvd_fact hp],
  exact ⟨λ h, h.elim (le_of_dvd (succ_pos _)) le_succ_of_le,
    λ h, (_root_.lt_or_eq_of_le h).elim (or.inr ∘ le_of_lt_succ)
      (λ h, or.inl $ by rw h)⟩
end

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

section
open list

lemma mem_list_primes_of_dvd_prod {p : ℕ} (hp : prime p) :
  ∀ {l : list ℕ}, (∀ p ∈ l, prime p) → p ∣ prod l → p ∈ l
| []       := λ h₁ h₂, absurd h₂ (prime.not_dvd_one hp)
| (q :: l) := λ h₁ h₂,
  have h₃ : p ∣ q * prod l := @prod_cons _ _ l q ▸ h₂,
  have hq : prime q := h₁ q (mem_cons_self _ _),
  or.cases_on ((prime.dvd_mul hp).1 h₃)
    (λ h, by rw [prime.dvd_iff_not_coprime hp, coprime_primes hp hq, ne.def, not_not] at h;
      exact h ▸ mem_cons_self _ _)
    (λ h, have hl : ∀ p ∈ l, prime p := λ p hlp, h₁ p ((mem_cons_iff _ _ _).2 (or.inr hlp)),
    (mem_cons_iff _ _ _).2 (or.inr (mem_list_primes_of_dvd_prod hl h)))

lemma mem_factors_iff_dvd {n p : ℕ} (hn : 0 < n) (hp : prime p) : p ∈ factors n ↔ p ∣ n :=
⟨λ h, prod_factors hn ▸ list.dvd_prod h,
 λ h, mem_list_primes_of_dvd_prod hp (@mem_factors n) ((prod_factors hn).symm ▸ h)⟩

lemma perm_of_prod_eq_prod : ∀ {l₁ l₂ : list ℕ}, prod l₁ = prod l₂ →
  (∀ p ∈ l₁, prime p) → (∀ p ∈ l₂, prime p) → l₁ ~ l₂
| []        []        _  _  _  := perm.nil
| []        (a :: l)  h₁ h₂ h₃ :=
  have ha : a ∣ 1 := @prod_nil ℕ _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _,
  absurd ha (prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
| (a :: l)  []        h₁ h₂ h₃ :=
  have ha : a ∣ 1 := @prod_nil ℕ _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _,
  absurd ha (prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
| (a :: l₁) (b :: l₂) h hl₁ hl₂ :=
  have hl₁' : ∀ p ∈ l₁, prime p := λ p hp, hl₁ p (mem_cons_of_mem _ hp),
  have hl₂' : ∀ p ∈ (b :: l₂).erase a, prime p := λ p hp, hl₂ p (mem_of_mem_erase hp),
  have ha : a ∈ (b :: l₂) := mem_list_primes_of_dvd_prod (hl₁ a (mem_cons_self _ _)) hl₂
    (h ▸ by rw prod_cons; exact dvd_mul_right _ _),
  have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_erase ha,
  have hl : prod l₁ = prod ((b :: l₂).erase a) :=
  (nat.mul_left_inj (prime.pos (hl₁ a (mem_cons_self _ _)))).1 $
    by rwa [← prod_cons, ← prod_cons, ← prod_eq_of_perm hb],
  perm.trans (perm.skip _ (perm_of_prod_eq_prod hl hl₁' hl₂')) hb.symm

lemma factors_unique {n : ℕ} {l : list ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, prime p) : l ~ factors n :=
have hn : 0 < n := nat.pos_of_ne_zero $ λ h, begin
  rw h at *, clear h,
  induction l with a l hi,
  { exact absurd h₁ dec_trivial },
  { rw prod_cons at h₁,
    exact nat.mul_ne_zero (ne_of_lt (prime.pos (h₂ a (mem_cons_self _ _)))).symm
      (hi (λ p hp, h₂ p (mem_cons_of_mem _ hp))) h₁ }
end,
perm_of_prod_eq_prod (by rwa prod_factors hn) h₂ (@mem_factors _)

end

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : prime p) {m n k l : ℕ}
      (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k+l+1) ∣ m*n) :
      p ^ (k+1) ∣ m ∨ p ^ (l+1) ∣ n :=
have hpd : p^(k+l) * p ∣ m*n, from hpmn,
have hpd2 : p ∣ (m*n) / p ^ (k+l), from dvd_div_of_mul_dvd hpd,
have hpd3 : p ∣ (m*n) / (p^k * p^l), by simpa [nat.pow_add] using hpd2,
have hpd4 : p ∣ (m / p^k) * (n / p^l), by simpa [nat.div_mul_div hpm hpn] using hpd3,
have hpd5 : p ∣ (m / p^k) ∨ p ∣ (n / p^l), from (prime.dvd_mul p_prime).1 hpd4,
show p^k*p ∣ m ∨ p^l*p ∣ n, from
  hpd5.elim
    (assume : p ∣ m / p ^ k, or.inl $ mul_dvd_of_dvd_div hpm this)
    (assume : p ∣ n / p ^ l, or.inr $ mul_dvd_of_dvd_div hpn this)

end nat

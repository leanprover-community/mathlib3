/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.nat.factors
import data.nat.prime
import tactic.norm_num

/-!
# Primality prover

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a `norm_num` extention to prove that natural numbers are prime.

-/

namespace tactic
namespace norm_num

lemma is_prime_helper (n : ℕ)
  (h₁ : 1 < n) (h₂ : nat.min_fac n = n) : nat.prime n :=
nat.prime_def_min_fac.2 ⟨h₁, h₂⟩

lemma min_fac_bit0 (n : ℕ) : nat.min_fac (bit0 n) = 2 :=
by simp [nat.min_fac_eq, show 2 ∣ bit0 n, by simp [bit0_eq_two_mul n]]

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def min_fac_helper (n k : ℕ) : Prop :=
0 < k ∧ bit1 k ≤ nat.min_fac (bit1 n)

theorem min_fac_helper.n_pos {n k : ℕ} (h : min_fac_helper n k) : 0 < n :=
pos_iff_ne_zero.2 $ λ e,
by rw e at h; exact not_le_of_lt (nat.bit1_lt h.1) h.2

lemma min_fac_ne_bit0 {n k : ℕ} : nat.min_fac (bit1 n) ≠ bit0 k :=
begin
  rw bit0_eq_two_mul,
  refine (λ e, absurd ((nat.dvd_add_iff_right _).2
    (dvd_trans ⟨_, e⟩ (nat.min_fac_dvd _))) _); simp
end

lemma min_fac_helper_0 (n : ℕ) (h : 0 < n) : min_fac_helper n 1 :=
begin
  refine ⟨zero_lt_one, lt_of_le_of_ne _ min_fac_ne_bit0.symm⟩,
  rw nat.succ_le_iff,
  refine lt_of_le_of_ne (nat.min_fac_pos _) (λ e, nat.not_prime_one _),
  rw e,
  exact nat.min_fac_prime (nat.bit1_lt h).ne',
end

lemma min_fac_helper_1 {n k k' : ℕ} (e : k + 1 = k')
  (np : nat.min_fac (bit1 n) ≠ bit1 k)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  rw ← e,
  refine ⟨nat.succ_pos _,
    (lt_of_le_of_ne (lt_of_le_of_ne _ _ : k+1+k < _)
      min_fac_ne_bit0.symm : bit0 (k+1) < _)⟩,
  { rw add_right_comm, exact h.2 },
  { rw add_right_comm, exact np.symm }
end

lemma min_fac_helper_2 (n k k' : ℕ) (e : k + 1 = k')
  (np : ¬ nat.prime (bit1 k)) (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  intro e₁, rw ← e₁ at np,
  exact np (nat.min_fac_prime $ ne_of_gt $ nat.bit1_lt h.n_pos)
end

lemma min_fac_helper_3 (n k k' c : ℕ) (e : k + 1 = k')
  (nc : bit1 n % bit1 k = c) (c0 : 0 < c)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  refine mt _ (ne_of_gt c0), intro e₁,
  rw [← nc, ← nat.dvd_iff_mod_eq_zero, ← e₁],
  apply nat.min_fac_dvd
end

lemma min_fac_helper_4 (n k : ℕ) (hd : bit1 n % bit1 k = 0)
  (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 k :=
by { rw ← nat.dvd_iff_mod_eq_zero at hd,
  exact le_antisymm (nat.min_fac_le_of_dvd (nat.bit1_lt h.1) hd) h.2 }

lemma min_fac_helper_5 (n k k' : ℕ) (e : bit1 k * bit1 k = k')
  (hd : bit1 n < k') (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 n :=
begin
  refine (nat.prime_def_min_fac.1 (nat.prime_def_le_sqrt.2
    ⟨nat.bit1_lt h.n_pos, _⟩)).2,
  rw ← e at hd,
  intros m m2 hm md,
  have := le_trans h.2 (le_trans (nat.min_fac_le_of_dvd m2 md) hm),
  rw nat.le_sqrt at this,
  exact not_le_of_lt hd this
end

open _root_.norm_num

/-- Given `e` a natural numeral and `d : nat` a factor of it, return `⊢ ¬ prime e`. -/
meta def prove_non_prime (e : expr) (n d₁ : ℕ) : tactic expr :=
do let e₁ := reflect d₁,
  c ← mk_instance_cache `(nat),
  (c, p₁) ← prove_lt_nat c `(1) e₁,
  let d₂ := n / d₁, let e₂ := reflect d₂,
  (c, e', p) ← prove_mul_nat c e₁ e₂,
  guard (e' =ₐ e),
  (c, p₂) ← prove_lt_nat c `(1) e₂,
  return $ `(@nat.not_prime_mul').mk_app [e₁, e₂, e, p, p₁, p₂]

/-- Given `a`,`a1 := bit1 a`, `n1` the value of `a1`, `b` and `p : min_fac_helper a b`,
  returns `(c, ⊢ min_fac a1 = c)`. -/
meta def prove_min_fac_aux (a a1 : expr) (n1 : ℕ) :
  instance_cache → expr → expr → tactic (instance_cache × expr × expr)
| ic b p := do
  k ← b.to_nat,
  let k1 := bit1 k,
  let b1 := `(bit1:ℕ→ℕ).mk_app [b],
  if n1 < k1*k1 then do
    (ic, e', p₁) ← prove_mul_nat ic b1 b1,
    (ic, p₂) ← prove_lt_nat ic a1 e',
    return (ic, a1, `(min_fac_helper_5).mk_app [a, b, e', p₁, p₂, p])
  else let d := k1.min_fac in
  if to_bool (d < k1) then do
    let k' := k+1, let e' := reflect k',
    (ic, p₁) ← prove_succ ic b e',
    p₂ ← prove_non_prime b1 k1 d,
    prove_min_fac_aux ic e' $ `(min_fac_helper_2).mk_app [a, b, e', p₁, p₂, p]
  else do
    let nc := n1 % k1,
    (ic, c, pc) ← prove_div_mod ic a1 b1 tt,
    if nc = 0 then
      return (ic, b1, `(min_fac_helper_4).mk_app [a, b, pc, p])
    else do
      (ic, p₀) ← prove_pos ic c,
      let k' := k+1, let e' := reflect k',
      (ic, p₁) ← prove_succ ic b e',
      prove_min_fac_aux ic e' $ `(min_fac_helper_3).mk_app [a, b, e', c, p₁, pc, p₀, p]

/-- Given `a` a natural numeral, returns `(b, ⊢ min_fac a = b)`. -/
meta def prove_min_fac (ic : instance_cache) (e : expr) : tactic (instance_cache × expr × expr) :=
match match_numeral e with
| match_numeral_result.zero := return (ic, `(2:ℕ), `(nat.min_fac_zero))
| match_numeral_result.one := return (ic, `(1:ℕ), `(nat.min_fac_one))
| match_numeral_result.bit0 e := return (ic, `(2), `(min_fac_bit0).mk_app [e])
| match_numeral_result.bit1 e := do
  n ← e.to_nat,
  c ← mk_instance_cache `(nat),
  (c, p) ← prove_pos c e,
  let a1 := `(bit1:ℕ→ℕ).mk_app [e],
  prove_min_fac_aux e a1 (bit1 n) c `(1) (`(min_fac_helper_0).mk_app [e, p])
| _ := failed
end

/-- A partial proof of `factors`. Asserts that `l` is a sorted list of primes, lower bounded by a
prime `p`, which multiplies to `n`. -/
def factors_helper (n p : ℕ) (l : list ℕ) : Prop :=
p.prime → list.chain (≤) p l ∧ (∀ a ∈ l, nat.prime a) ∧ list.prod l = n

lemma factors_helper_nil (a : ℕ) : factors_helper 1 a [] :=
λ pa, ⟨list.chain.nil, by rintro _ ⟨⟩, list.prod_nil⟩

lemma factors_helper_cons' (n m a b : ℕ) (l : list ℕ)
  (h₁ : b * m = n) (h₂ : a ≤ b) (h₃ : nat.min_fac b = b)
  (H : factors_helper m b l) : factors_helper n a (b :: l) :=
λ pa,
  have pb : b.prime, from nat.prime_def_min_fac.2 ⟨le_trans pa.two_le h₂, h₃⟩,
  let ⟨f₁, f₂, f₃⟩ := H pb in
  ⟨list.chain.cons h₂ f₁, λ c h, h.elim (λ e, e.symm ▸ pb) (f₂ _),
   by rw [list.prod_cons, f₃, h₁]⟩

lemma factors_helper_cons (n m a b : ℕ) (l : list ℕ)
  (h₁ : b * m = n) (h₂ : a < b) (h₃ : nat.min_fac b = b)
  (H : factors_helper m b l) : factors_helper n a (b :: l) :=
factors_helper_cons' _ _ _ _ _ h₁ h₂.le h₃ H

lemma factors_helper_sn (n a : ℕ) (h₁ : a < n) (h₂ : nat.min_fac n = n) : factors_helper n a [n] :=
factors_helper_cons _ _ _ _ _ (mul_one _) h₁ h₂ (factors_helper_nil _)

lemma factors_helper_same (n m a : ℕ) (l : list ℕ) (h : a * m = n)
  (H : factors_helper m a l) : factors_helper n a (a :: l) :=
λ pa, factors_helper_cons' _ _ _ _ _ h le_rfl (nat.prime_def_min_fac.1 pa).2 H pa

lemma factors_helper_same_sn (a : ℕ) : factors_helper a a [a] :=
factors_helper_same _ _ _ _ (mul_one _) (factors_helper_nil _)

lemma factors_helper_end (n : ℕ) (l : list ℕ) (H : factors_helper n 2 l) : nat.factors n = l :=
let ⟨h₁, h₂, h₃⟩ := H nat.prime_two in
have _, from list.chain'_iff_pairwise.1 (@list.chain'.tail _ _ (_::_) h₁),
(list.eq_of_perm_of_sorted (nat.factors_unique h₃ h₂) this (nat.factors_sorted _)).symm

/-- Given `n` and `a` natural numerals, returns `(l, ⊢ factors_helper n a l)`. -/
meta def prove_factors_aux :
  instance_cache → expr → expr → ℕ → ℕ → tactic (instance_cache × expr × expr)
| c en ea n a :=
  let b := n.min_fac in
  if b < n then do
    let m := n / b,
    (c, em) ← c.of_nat m,
    if b = a then do
      (c, _, p₁) ← prove_mul_nat c ea em,
      (c, l, p₂) ← prove_factors_aux c em ea m a,
      pure (c, `(%%ea::%%l:list ℕ), `(factors_helper_same).mk_app [en, em, ea, l, p₁, p₂])
    else do
      (c, eb) ← c.of_nat b,
      (c, _, p₁) ← prove_mul_nat c eb em,
      (c, p₂) ← prove_lt_nat c ea eb,
      (c, _, p₃) ← prove_min_fac c eb,
      (c, l, p₄) ← prove_factors_aux c em eb m b,
      pure (c, `(%%eb::%%l : list ℕ),
        `(factors_helper_cons).mk_app [en, em, ea, eb, l, p₁, p₂, p₃, p₄])
  else if b = a then
    pure (c, `([%%ea] : list ℕ), `(factors_helper_same_sn).mk_app [ea])
  else do
    (c, p₁) ← prove_lt_nat c ea en,
    (c, _, p₂) ← prove_min_fac c en,
    pure (c, `([%%en] : list ℕ), `(factors_helper_sn).mk_app [en, ea, p₁, p₂])

/-- Evaluates the `prime` and `min_fac` functions. -/
@[norm_num] meta def eval_prime : expr → tactic (expr × expr)
| `(nat.prime %%e) := do
  n ← e.to_nat,
  match n with
  | 0 := false_intro `(nat.not_prime_zero)
  | 1 := false_intro `(nat.not_prime_one)
  | _ := let d₁ := n.min_fac in
    if d₁ < n then prove_non_prime e n d₁ >>= false_intro
    else do
      let e₁ := reflect d₁,
      c ← mk_instance_cache `(ℕ),
      (c, p₁) ← prove_lt_nat c `(1) e₁,
      (c, e₁, p) ← prove_min_fac c e,
      true_intro $ `(is_prime_helper).mk_app [e, p₁, p]
  end
| `(nat.min_fac %%e) := do
  ic ← mk_instance_cache `(ℕ),
  prod.snd <$> prove_min_fac ic e
| `(nat.factors %%e) := do
  n ← e.to_nat,
  match n with
  | 0 := pure (`(@list.nil ℕ), `(nat.factors_zero))
  | 1 := pure (`(@list.nil ℕ), `(nat.factors_one))
  | _ := do
    c ← mk_instance_cache `(ℕ),
    (c, l, p) ← prove_factors_aux c e `(2) n 2,
    pure (l, `(factors_helper_end).mk_app [e, l, p])
  end
| _ := failed

end norm_num
end tactic

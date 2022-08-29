/-
Copyright (c) 2022 Michael Stol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stol
-/
import number_theory.legendre_symbol.quadratic_reciprocity

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobi_sym a b` for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `zmod.legendre_sym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via a variant of `nat.factors`, `nat.prime_factors`,
that includes the information that the factors are primes. Since `nat.factors 0 = []`,
this implies in particular that `jacobi_sym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Legendre symbol, including the following.

* Multiplicativity in both arguments (`jacobi_sym_mul_left`, `jacobi_sym_mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
  (`jacobi_sym_eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
  (`jacobi_sym_eq_zero_iff`)

* If the symbol has the value `-1`, then `a : zmod b` is not a square (`jacobi_sym_eq_neg_one`)

* Quadratic reciprocity (`jacobi_sym_quadratic_reciprocity`,
  `jacobi_sym_quadratic_reciprocity_one_mod_four`,
  `jacobi_sym_quadratic_reciprocity_threee_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobi_sym_neg_one`, `jacobi_sym_two`,
  `jacobi_sym_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobi_sym_mod_left`)
  and on `b` only via its residue class mod `4*a` (`jacobi_sym_mod_right`)

## Notations

We define the notation `[a | b]ⱼ` for `legendre_sym a b`, localized to `number_theory_symbols`.

## Implementation notes

We implement a variant `nat.prime_factors` of `nat.factors` that returns a `list primes`
and use this for the definition of the Jacobi symbol (we need the information that the
factors are prime for the Legendre symbols in the product to be defined).

## Tags
Jacobi symbol, quadratic reciprocity
-/

section prime_factors

/-!
### A version of `nat.factors` that knows that the factors are primes
-/

namespace nat

/-- `nat.prime_factors n` produces the ordered list of prime factors of `n`,
as terms of type `nat.primes`. -/
def prime_factors (n : ℕ) : list primes :=
n.factors.attach.map (λ p : {x // x ∈ n.factors}, ⟨p.1, prime_of_mem_factors p.2⟩)

/-- Coercing the primes in `nat.prime_factors n` to be naturals gives back `nat.factors n`. -/
lemma prime_factors.to_factors (n : ℕ) : n.prime_factors.map (coe : primes → ℕ) = n.factors :=
begin
  have h : (coe : primes → ℕ)
           ∘ (λ p : {x // x ∈ n.factors}, (⟨p.1, prime_of_mem_factors p.2⟩ : primes))
            = λ p, p.1,
  { ext, simp only [function.comp_app, subtype.coe_mk], },
  rw [prime_factors, list.map_map, h, list.attach_map_val],
end

lemma coe_list_primes_inj : function.injective (list.map (coe : primes → ℕ)) :=
list.map_injective_iff.mpr primes.coe_nat_inj

lemma coe_list_primes_perm (l₁ l₂ : list primes) (h : l₁.map (coe : primes → ℕ) ~ l₂.map coe) :
  l₁ ~ l₂ :=
begin
  rw ← multiset.coe_eq_coe at h ⊢,
  simp_rw ← multiset.coe_map at h,
  exact multiset.map_injective primes.coe_nat_inj h,
end

/-- The list of prime factors of `0` is empty. -/
lemma prime_factors_zero : prime_factors 0 = [] :=
begin
  apply_fun (list.map (coe : primes → ℕ)) using coe_list_primes_inj,
  simp only [prime_factors.to_factors, list.map, factors_zero],
end

/-- The list of prime factors of `1` is empty. -/
lemma prime_factors_one : prime_factors 1 = [] :=
begin
  apply_fun (list.map (coe : primes → ℕ)) using coe_list_primes_inj,
  simp only [prime_factors.to_factors, list.map, factors_one],
end

/-- Turn a natural number `p` that is known to be prime into a term of type `primes`. -/
def to_primes (p : ℕ) [fact p.prime] : primes := ⟨p, fact.out p.prime⟩

@[simp]
lemma coe_to_primes_eq_self (p : ℕ) [fact p.prime] : (p.to_primes : ℕ) = p := rfl

/-- If `p` is prime, then its list of prime factors is `[p]`. -/
lemma prime_factors_prime (p : ℕ) [fp : fact p.prime] : p.prime_factors = [p.to_primes] :=
begin
  apply_fun (list.map (coe : primes → ℕ)) using coe_list_primes_inj,
  simp only [factors_prime fp.1, prime_factors.to_factors, list.map, coe_to_primes_eq_self,
             eq_self_iff_true, and_self],
end

/-- The list of prime factors of `m * n` is a permutation of the concatenation
of the lists of prime factors of `m` and that of `n`. -/
lemma perm_prime_factors_mul (m n : ℕ) [ne_zero m] [ne_zero n] :
  (m * n).prime_factors ~ m.prime_factors ++ n.prime_factors :=
begin
  apply coe_list_primes_perm,
  simp_rw [list.map_append, prime_factors.to_factors],
  exact perm_factors_mul (ne_zero.ne m) (ne_zero.ne n),
end

end nat

end prime_factors

/-!
### Some helpful lemmas
-/

namespace nat

/-- An odd natural number is non-zero. -/
-- This doesn't work inlined when `n` is a more complicated expression.
lemma ne_zero_of_odd {n : ℕ} (h : odd n) : n ≠ 0 := ne_of_odd_add h

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
lemma odd_mod_of_odd {n a : ℕ} (hn : odd n) (ha : even a) : odd (n % a) :=
begin
  have h := (@nat.odd_add (n % a) (a * (n / a))).mp,
  rw [mod_add_div n a] at h,
  exact (h hn).mpr (even.mul_right ha _),
end

end nat

namespace int

/-- If the gcd of `a` with `m * n` is not one, then `gcd a m ≠ 1` or `gcd a n ≠ 1`. -/
lemma gcd_ne_one_of_gcd_mul_ne_one {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) ≠ 1) :
  a.gcd m ≠ 1 ∨ a.gcd n ≠ 1 :=
begin
  by_contra' h₁,
  exact h (gcd_eq_one_iff_coprime.mpr $
    is_coprime.mul_right (gcd_eq_one_iff_coprime.mp h₁.left) $ gcd_eq_one_iff_coprime.mp h₁.right)
end

end int

namespace zmod

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : zmod p` is nonzero. -/
lemma ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p = 1) :
  (a : zmod p) ≠ 0 :=
begin -- this should have a simpler proof!
  intro hf,
  rw int_coe_zmod_eq_zero_iff_dvd a p at hf,
  have h' := int.dvd_gcd hf (dvd_refl p),
  rw h at h',
  norm_cast at h',
  exact pp.not_dvd_one h',
end

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : zmod p` is zero. -/
lemma eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p ≠ 1) :
  (a : zmod p) = 0 :=
begin
  rw int_coe_zmod_eq_zero_iff_dvd a p,
  have hr := int.gcd_dvd_right a p, norm_cast at hr,
  have hl := int.gcd_dvd_left a p,
  rwa ← (nat.prime.dvd_iff_eq pp h).mp hr at hl,
end

end zmod

section jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol `(a / b)` for integers `a` and natural numbers `b` as the
product of the legendre symbols `(a / p)`, where `p` runs through the prime divisors
(with multiplicity) of `b`, as provided by `b.factors`. This agrees with the Jacobi symbol
when `b` is odd and gives less meaningful values when it is not (e.g., the symbol is `1`
when `b = 0`). This is called `jacobi_sym a b`.

We define localized notation (locale `number_theory_symbols`) `[a | b]ⱼ` for the Jacobi
symbol `jacobi_sym a b`. (Unfortunately, there is no subscript "J" in unicode.)
-/

open zmod nat

/-- The Jacobi symbol of `a` and `b` -/
def jacobi_sym (a : ℤ) (b : ℕ) : ℤ :=
(b.prime_factors.map (λ (p : primes), @legendre_sym p.1 ⟨p.2⟩ a)).prod

-- Notation for the Jacobi symbol.
localized "notation `[` a ` | ` b `]ⱼ` := jacobi_sym a b" in number_theory_symbols

/-!
### Properties of the Jacobi symbol
-/

open_locale number_theory_symbols

/-- The Jacobi symbol `(a / 0)` has the value `1`. -/
lemma jacobi_sym_zero_right (a : ℤ) : [a | 0]ⱼ = 1 :=
by simp only [jacobi_sym, prime_factors_zero, list.map_nil, list.prod_nil]

/-- The Jacobi symbol `(a / 1)` has the value `1`. -/
lemma jacobi_sym_one_right (a : ℤ) : [a | 1]ⱼ = 1 :=
by simp only [jacobi_sym, prime_factors_one, list.map_nil, list.prod_nil]

/-- The Legendre symbol `(a / p)` with an integer `a` and a prime number `p`
is the same as the Jaocbi symbol `(a / p)`. -/
lemma legendre_sym.to_jacobi_sym {p : ℕ} [fp : fact p.prime] {a : ℤ} :
  legendre_sym p a = [a | p]ⱼ :=
by simp only [jacobi_sym, prime_factors_prime p, subtype.val_eq_coe, coe_to_primes_eq_self,
              list.map, list.prod_cons, list.prod_nil, mul_one]

/-- The Jacobi symbol is multiplicative in its second argument. -/
lemma jacobi_sym_mul_right (a : ℤ) (b₁ b₂ : ℕ) [ne_zero b₁] [ne_zero b₂] :
  [a | b₁ * b₂]ⱼ = [a | b₁]ⱼ * [a | b₂]ⱼ :=
by simp_rw [jacobi_sym,
            list.perm.prod_eq (list.perm.map (λ p : primes, @legendre_sym p.1 ⟨p.2⟩ a)
                                             (perm_prime_factors_mul b₁ b₂)),
            list.map_append, list.prod_append]

/-- The Jacobi symbol `(1 / b)` has the value `1`. -/
lemma jacobi_sym_one_left (b : ℕ) : [1 | b]ⱼ = 1 :=
begin
  let P : ℕ → Prop := λ b, [1 | b]ⱼ = 1,
  have hp : ∀ p : ℕ, p.prime → P p,
  { intros p pp,
    haveI : fact p.prime := ⟨pp⟩,
    simp_rw [P, ← legendre_sym.to_jacobi_sym, legendre_sym_one], },
  have hmul : ∀ m n : ℕ, P m → P n → P (m * n),
  { intros m n hm hn,
    simp_rw [P] at hm hn ⊢,
    by_cases hm0 : m = 0,
    { rw [hm0, zero_mul, jacobi_sym_zero_right], },
    by_cases hn0 : n = 0,
    { rw [hn0, mul_zero, jacobi_sym_zero_right], },
    haveI : ne_zero m := ⟨hm0⟩,
    haveI : ne_zero n := ⟨hn0⟩,
    rw [jacobi_sym_mul_right, hm, hn, one_mul], },
  exact rec_on_mul (jacobi_sym_zero_right 1) (jacobi_sym_one_right 1) hp hmul b,
end

/-- The Jacobi symbol is multiplicative in its first argument. -/
lemma jacobi_sym_mul_left (a₁ a₂ : ℤ) (b : ℕ) : [a₁ * a₂ | b]ⱼ = [a₁ | b]ⱼ * [a₂ | b]ⱼ :=
begin
  let P : ℕ → Prop := λ b, [a₁ * a₂ | b]ⱼ = [a₁ | b]ⱼ * [a₂ | b]ⱼ,
  have h0 : P 0,
  { simp_rw [P, jacobi_sym, prime_factors_zero, list.map_nil, list.prod_nil, one_mul], },
  have h1 : P 1,
  { simp_rw [P, jacobi_sym, prime_factors_one, list.map_nil, list.prod_nil, one_mul], },
  have hp : ∀ p : ℕ, p.prime → P p,
  { intros p pp,
    haveI : fact p.prime := ⟨pp⟩,
    simp_rw [P, ← legendre_sym.to_jacobi_sym, legendre_sym_mul], },
  have h : ∀ m n : ℕ, P m → P n → P (m * n),
  { intros m n hm hn,
    simp_rw [P] at hm hn ⊢,
    by_cases hmz : m = 0,
    { rw [hmz, zero_mul], exact h0, },
    by_cases hnz : n = 0,
    { rw [hnz, mul_zero], exact h0, },
    haveI : ne_zero m := ⟨hmz⟩,
    haveI : ne_zero n := ⟨hnz⟩,
    simp_rw [jacobi_sym_mul_right, hm, hn, mul_mul_mul_comm], },
  exact rec_on_mul h0 h1 hp h b,
end

/-- We have that `(a^e / b) = (a / b)^e` for the Jacobi symbol. -/
lemma jacobi_sym_pow_left (a : ℤ) (e b : ℕ) : [a ^ e | b]ⱼ = [a | b]ⱼ ^ e :=
begin
  induction e with e ih,
  { rw [pow_zero, pow_zero, jacobi_sym_one_left], },
  { rw [pow_succ, pow_succ, jacobi_sym_mul_left, ih], }
end

/-- We have that `(a / b^e) = (a / b)^e` for the Jacobi symbol. -/
lemma jacobi_sym_pow_right (a : ℤ) (b e : ℕ) : [a | b ^ e]ⱼ = [a | b]ⱼ ^ e :=
begin
  induction e with e ih,
  { rw [pow_zero, pow_zero, jacobi_sym_one_right], },
  { by_cases hb : b = 0,
    { rw [hb, zero_pow (succ_pos e), jacobi_sym_zero_right, one_pow], },
    { haveI : ne_zero b := ⟨hb⟩,
      haveI : ne_zero (b ^ e) := ⟨pow_ne_zero e hb⟩,
      rw [pow_succ, pow_succ, jacobi_sym_mul_right, ih], } }
end

/-- The Jacobi symbol `(a / b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
lemma jacobi_sym_eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) :
  [a | b]ⱼ = 1 ∨ [a | b]ⱼ = -1 :=
begin
  let P := λ b : ℕ, a.gcd b = 1 → [a | b]ⱼ = 1 ∨ [a | b]ⱼ = -1,
  have hp : ∀ p : ℕ, p.prime → P p,
  { intros p pp hpg,
    haveI : fact p.prime := ⟨pp⟩,
    simp_rw [← legendre_sym.to_jacobi_sym],
    exact legendre_sym_eq_one_or_neg_one p (ne_zero_of_gcd_eq_one pp hpg), },
  have hmul : ∀ m n : ℕ, P m → P n → P (m * n),
  { intros m n hm hn hmng,
    rw [nat.cast_mul] at hmng,
    by_cases hm0 : m = 0,
    { rw [hm0, zero_mul],
      exact or.inl (jacobi_sym_zero_right a), },
    by_cases hn0 : n = 0,
    { rw [hn0, mul_zero],
      exact or.inl (jacobi_sym_zero_right a), },
    haveI : ne_zero m := ⟨hm0⟩,
    haveI : ne_zero n := ⟨hn0⟩,
    have hmg : a.gcd m = 1,
    { have t := int.gcd_dvd_gcd_mul_right_right a m n, rw hmng at t, exact nat.dvd_one.mp t,},
    have hng : a.gcd n = 1,
    { have t := int.gcd_dvd_gcd_mul_left_right a n m, rw hmng at t, exact nat.dvd_one.mp t,},
    simp_rw [jacobi_sym_mul_right],
    cases hm hmg with hl hr,
    { rw [hl, one_mul],
      exact hn hng, },
    { rw [hr, neg_mul, one_mul, neg_inj, neg_eq_iff_neg_eq],
      exact or.dcases_on (hn hng) or.inr (λ hr', or.inl hr'.symm), } },
  exact rec_on_mul (λ _, (or.inl $ jacobi_sym_zero_right a))
                   (λ _, (or.inl $ jacobi_sym_one_right a)) hp hmul b h,
end

/-- The square of the Jacobi symbol `(a / b)` is `1` when `a` and `b` are coprime. -/
lemma jacobi_sym_sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a | b]ⱼ ^ 2 = 1 :=
by cases jacobi_sym_eq_one_or_neg_one h with h₁ h₁; rw h₁; refl

/-- The Jacobi symbol `(a^2 / b)` is `1` when `a` and `b` are coprime. -/
lemma jacobi_sym_sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a ^ 2 | b]ⱼ = 1 :=
by rw [pow_two, jacobi_sym_mul_left, ← pow_two, jacobi_sym_sq_one h]

/-- The Jacobi symbol `(a / b)` depends only on `a` mod `b`. -/
lemma jacobi_sym_mod_left (a : ℤ) (b : ℕ) : [a | b]ⱼ = [a % b | b]ⱼ :=
begin
  -- we need to generalize over `a` here
  let P : ℕ → Prop := λ b, ∀ a : ℤ, [a | b]ⱼ = [a % b | b]ⱼ,
  have hp : ∀ p : ℕ, p.prime → P p,
  { intros p pp a,
    haveI : fact p.prime := ⟨pp⟩,
    simp_rw [← legendre_sym.to_jacobi_sym, legendre_sym_mod p a], },
  have hmul : ∀ m n : ℕ, P m → P n → P (m * n),
  { intros m n hm hn,
    by_cases hm0 : m = 0,
    { intro a, simp_rw [hm0, zero_mul, jacobi_sym_zero_right], },
    by_cases hn0 : n = 0,
    { intro a, simp_rw [hn0, mul_zero, jacobi_sym_zero_right], },
    haveI : ne_zero m := ⟨hm0⟩,
    haveI : ne_zero n := ⟨hn0⟩,
    intro a,
    simp_rw [nat.cast_mul, jacobi_sym_mul_right, hm a, hn a, hm (a % (m * n)), hn (a % (m * n))],
    rw [int.mod_mod_of_dvd a (dvd_mul_right ↑m ↑n), int.mod_mod_of_dvd a (dvd_mul_left ↑n ↑m)] },
  exact rec_on_mul (λ _, by simp_rw [jacobi_sym_zero_right])
                   (λ _, by simp_rw [jacobi_sym_one_right]) hp hmul b a,
end

/-- The Jacobi symbol `(a / b)` depends only on `a` mod `b`. -/
lemma jacobi_sym_mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : [a₁ | b]ⱼ = [a₂ | b]ⱼ :=
by rw [jacobi_sym_mod_left, h, ← jacobi_sym_mod_left]

/-- The Jacobi symbol `(a / b)` vanishes when `a` and `b` are not coprime and `b ≠ 0`. -/
lemma jacobi_sym_eq_zero_if_not_coprime {a : ℤ} {b : ℕ} [hb : ne_zero b] (h : a.gcd b ≠ 1) :
  [a | b]ⱼ = 0 :=
begin
  let P : ℕ → Prop := λ b, b ≠ 0 → a.gcd b ≠ 1 → [a | b]ⱼ = 0,
  have hp : ∀ p : ℕ, p.prime → P p,
  { intros p pp _ hg,
    haveI : fact p.prime := ⟨pp⟩,
    rw [← legendre_sym.to_jacobi_sym, legendre_sym_eq_zero_iff],
    exact eq_zero_of_gcd_ne_one pp hg, },
  have hmul : ∀ m n : ℕ, P m → P n → P (m * n),
  { intros m n hm hn hmn0 hg,
    haveI hm0 : ne_zero m := ⟨left_ne_zero_of_mul hmn0⟩,
    haveI hn0 : ne_zero n := ⟨right_ne_zero_of_mul hmn0⟩,
    rw [jacobi_sym_mul_right],
    cases int.gcd_ne_one_of_gcd_mul_ne_one hg with hgm hgn,
    { rw [hm hm0.1 hgm, zero_mul], },
    { rw [hn hn0.1 hgn, mul_zero], } },
  exact rec_on_mul (λ hf _, false.rec _ (hf rfl)) (λ _ h₁, false.rec _ (h₁ a.gcd_one_right))
                   hp hmul b (ne_zero.ne b) h,
end

/-- The Jacobi symbol `(a / b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
lemma jacobi_sym_eq_zero_iff {a : ℤ} {b : ℕ} : [a | b]ⱼ = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
begin
  refine ⟨λ h, ⟨λ hf, _, λ hf, _⟩, λ h, @jacobi_sym_eq_zero_if_not_coprime a b ⟨h.left⟩ h.right⟩,
  { rw [hf, jacobi_sym_zero_right a] at h,
    exact one_ne_zero h, },
  { have h₁ := jacobi_sym_eq_one_or_neg_one hf,
    rw [h] at h₁,
    exact or.dcases_on h₁ zero_ne_one (int.zero_ne_neg_of_ne zero_ne_one), }
end

/-- The Jacobi symbol `(0 / b)` vanishes when `b > 1`. -/
lemma jacobi_sym_zero_left {b : ℕ} (hb : 1 < b) : [0 | b]ⱼ = 0 :=
begin
  have h : (0 : ℤ).gcd b ≠ 1,
  { rw [int.gcd_zero_left, int.nat_abs_of_nat],
    exact (ne_of_lt hb).symm, },
  haveI : ne_zero b := ⟨ne_zero_of_lt hb⟩,
  exact jacobi_sym_eq_zero_if_not_coprime h,
end

/-- If the Jacobi symbol `(a / b)` is `-1`, then `a` is not a square modulo `b`. -/
lemma jacobi_sym_eq_neg_one {a : ℤ} {b : ℕ} (h : [a | b]ⱼ = -1) : ¬ is_square (a : zmod b) :=
begin
  haveI : fact (0 < b),
  { refine ⟨nat.pos_of_ne_zero (λ hf, _)⟩,
    have h₁ : [a | b]ⱼ ≠ 1 := by {rw h, dec_trivial},
    rw [hf, jacobi_sym_zero_right] at h₁,
    exact h₁ rfl, },
  rintro ⟨x, hx⟩,
  have hab : a % b = (x * x) % b,
  { have h₁ : (a : zmod b) = (x.val * x.val : ℤ),
    { simp only [hx, nat_cast_val, int.cast_mul, int_cast_cast, cast_id', id.def], },
    have h₂ := (zmod.int_coe_eq_int_coe_iff' a (x.val * x.val) b).mp h₁,
    rwa [zmod.nat_cast_val] at h₂, },
  have hj := jacobi_sym_mod_left' hab,
  rw [jacobi_sym_mul_left, h, ← pow_two] at hj,
  exact (-1 : ℤ).lt_irrefl (hj.substr (sq_nonneg [x | b]ⱼ)),
end

/-!
### Values at `-1`, `2` and `-2`
-/

/-- An induction principle that can be used for "multiplicative" induction to show
properties of odd natural numbers. -/
lemma nat.mul_induction_odd {P : ℕ → Prop} (h1 : P 1) (hp : ∀ p : ℕ, p.prime → p ≠ 2 → P p)
  (h : ∀ m n : ℕ, odd m → odd n → P m → P n → P (m * n)) (b : ℕ) (hb : odd b) : P b :=
rec_on_mul (λ h, false.rec _ (even_iff_not_odd.mp even_zero h)) (λ _, h1)
           (λ p pp p2, hp p pp ((@prime.mod_two_eq_one_iff_ne_two _ ⟨pp⟩).mp (odd_iff.mp p2)))
           (λ m n hm hn hmn, let hmo := odd.of_mul_left hmn in let hno := odd.of_mul_right hmn in
                             h m n hmo hno (hm hmo) (hn hno))
           b hb

/-- If `χ` is a multiplicative function such that `(a / p) = χ p` for all odd primes `p`,
then the Jacobi symbol `(a / b)` equals `χ b` for all odd natural numbers `b`. -/
lemma jacobi_sym_value (a : ℤ) {R : Type*} [comm_semiring R] (χ : R →* ℤ)
  (hp : ∀ (p : ℕ) (pp : p.prime) (h2 : p ≠ 2), @legendre_sym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : odd b) :
  [a | b]ⱼ = χ b :=
begin
  let P : ℕ → Prop := λ b, [a | b]ⱼ = χ b,
  have h1 : P 1,
  { simp_rw [P, jacobi_sym_one_right, nat.cast_one, map_one], },
  have hp' : ∀ p : ℕ, p.prime → p ≠ 2 → P p,
  { intros p pp p2,
    haveI : fact p.prime := ⟨pp⟩,
    simp_rw [P, ← legendre_sym.to_jacobi_sym, hp p pp p2], },
  have hmul : ∀ m n : ℕ, odd m → odd n → P m → P n → P (m * n),
  { intros m n hmo hno hm hn,
    simp_rw [P] at hm hn ⊢,
    haveI : ne_zero m := ⟨ne_zero_of_odd hmo⟩,
    haveI : ne_zero n := ⟨ne_zero_of_odd hno⟩,
    rw [nat.cast_mul, jacobi_sym_mul_right, hm, hn, map_mul], },
  exact nat.mul_induction_odd h1 hp' hmul b hb,
end

/-- If `b` is odd, then the Jacobi symbol `(-1 / b)` is given by `χ₄ b`. -/
lemma jacobi_sym_neg_one {b : ℕ} (hb : odd b) : [-1 | b]ⱼ = χ₄ b :=
jacobi_sym_value (-1) χ₄ (λ p pp h2, @legendre_sym_neg_one p ⟨pp⟩ h2) hb

/-- If `b` is odd, then `(-a / b) = χ₄ b * (a / b)`. -/
lemma jacobi_sym_neg (a : ℤ) {b : ℕ} (hb : odd b) : [-a | b]ⱼ = χ₄ b * [a | b]ⱼ :=
by rw [neg_eq_neg_one_mul, jacobi_sym_mul_left, jacobi_sym_neg_one hb]

/-- If `b` is odd, then the Jacobi symbol `(2 / b)` is given by `χ₈ b`. -/
lemma jacobi_sym_two {b : ℕ} (hb : odd b) : [2 | b]ⱼ = χ₈ b :=
jacobi_sym_value 2 χ₈ (λ p pp h2, @legendre_sym_two p ⟨pp⟩ h2) hb

/-- If `b` is odd, then the Jacobi symbol `(-2 / b)` is given by `χ₈' b`. -/
lemma jacobi_sym_neg_two {b : ℕ} (hb : odd b) : [-2 | b]ⱼ = χ₈' b :=
jacobi_sym_value (-2) χ₈' (λ p pp h2, @legendre_sym_neg_two p ⟨pp⟩ h2) hb


/-!
### Quadratic Reciprocity
-/

/-- The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity -/
def qr_sign (m n : ℕ) : ℤ := [χ₄ m | n]ⱼ

/-- We can express `qr_sign m n` as a power of `-1` when `m` and `n` are odd. -/
lemma qr_sign_neg_one_pow {m n : ℕ} (hm : odd m) (hn : odd n) :
  qr_sign m n = (-1) ^ ((m / 2) * (n / 2)) :=
begin
  rw [qr_sign, pow_mul, ← χ₄_eq_neg_one_pow (nat.odd_iff.mp hm)],
  cases odd_mod_four_iff.mp (odd_iff.mp hm) with h h,
  { rw [χ₄_nat_one_mod_four h, jacobi_sym_one_left, one_pow], },
  { rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (nat.odd_iff.mp hn), jacobi_sym_neg_one hn], }
end

/-- When `m` and `n` are odd, then the square of `qr_sign m n` is `1`. -/
lemma qr_sign_sq_eq_one {m n : ℕ} (hm : odd m) (hn : odd n) : (qr_sign m n) ^ 2 = 1 :=
by rw [qr_sign_neg_one_pow hm hn, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- `qr_sign` is multiplicative in the first argument. -/
lemma qr_sign_mul_left (m₁ m₂ n : ℕ) : qr_sign (m₁ * m₂) n = qr_sign m₁ n * qr_sign m₂ n :=
by simp_rw [qr_sign, nat.cast_mul, map_mul, jacobi_sym_mul_left]

/-- `qr_sign` is multiplicative in the second argument. -/
lemma qr_sign_mul_right (m n₁ n₂ : ℕ) [ne_zero n₁] [ne_zero n₂] :
  qr_sign m (n₁ * n₂) = qr_sign m n₁ * qr_sign m n₂ :=
jacobi_sym_mul_right (χ₄ m) n₁ n₂

/-- `qr_sign` is symmetric when both arguments are odd. -/
lemma qr_sign_symm {m n : ℕ} (hm : odd m) (hn : odd n) : qr_sign m n = qr_sign n m :=
by rw [qr_sign_neg_one_pow hm hn, qr_sign_neg_one_pow hn hm, mul_comm (m / 2)]

/-- We can move `qr_sign m n` from one side of an equality to the other when `m` and `n` are odd. -/
lemma qr_sign_eq_iff_eq {m n : ℕ} (hm : odd m) (hn : odd n) (x y : ℤ) :
  qr_sign m n * x = y ↔ x = qr_sign m n * y :=
begin
  refine ⟨λ h', have h : _, from h'.symm, _, λ h, _⟩;
  rw [h, ← mul_assoc, ← pow_two, qr_sign_sq_eq_one hm hn, one_mul],
end

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma jacobi_sym_quadratic_reciprocity' {a b : ℕ} (ha : odd a) (hb : odd b) :
  [a | b]ⱼ = qr_sign b a * [b | a]ⱼ :=
begin
  -- `jacobi_sym_value _ χ` with `χ : R →* ℤ` (`R` a commutative semiring) introduces
  -- a cast `coe : ℕ → R` even when `R = ℕ`. The following is used to get rid of that later.
  have coe_nat_nat : ∀ a : ℕ, (coe : ℕ → ℕ) a = a := λ a, rfl,
  -- define the right hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : Π a : ℕ, ℕ →* ℤ := λ a,
  { to_fun := λ x, qr_sign x a * [x | a]ⱼ,
    map_one' := by rw [nat.cast_one, qr_sign, χ₄_nat_one_mod_four (by norm_num : 1 % 4 = 1),
                       jacobi_sym_one_left, mul_one],
    map_mul' := λ x y, by rw [qr_sign_mul_left, nat.cast_mul, jacobi_sym_mul_left,
                              mul_mul_mul_comm] },
  have rhs_apply : ∀ (a b : ℕ), rhs a b = qr_sign b a * [b | a]ⱼ := λ a b, rfl,
  refine jacobi_sym_value a (rhs a) (λ p pp hp, eq.symm _) hb,
  have hpo := pp.eq_two_or_odd'.resolve_left hp,
  rw [@legendre_sym.to_jacobi_sym p ⟨pp⟩, rhs_apply, coe_nat_nat,
      qr_sign_eq_iff_eq hpo ha, qr_sign_symm hpo ha],
  refine jacobi_sym_value p (rhs p) (λ q pq hq, _) ha,
  have hqo := pq.eq_two_or_odd'.resolve_left hq,
  rw [rhs_apply, coe_nat_nat, ← @legendre_sym.to_jacobi_sym p ⟨pp⟩, qr_sign_symm hqo hpo,
      qr_sign_neg_one_pow hpo hqo, @quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq],
end

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma jacobi_sym_quadratic_reciprocity {a b : ℕ} (ha : odd a) (hb : odd b) :
  [a | b]ⱼ = (-1) ^ ((a / 2) * (b / 2)) * [b | a]ⱼ :=
by rw [← qr_sign_neg_one_pow ha hb, qr_sign_symm ha hb, jacobi_sym_quadratic_reciprocity' ha hb]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are odd natural numbers
and `a % 4 = 1`, then `(a / b) = (b / a)`. -/
theorem jacobi_sym_quadratic_reciprocity_one_mod_four {a b : ℕ}  (ha : a % 4 = 1) (hb : odd b) :
  [a | b]ⱼ = [b | a]ⱼ :=
by rw [jacobi_sym_quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb,
       pow_mul, neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]

/-- The Law of Quadratic Reciprocityfor the Jacobi symbol: if `a` and `b` are odd natural numbers
both congruent to `3` mod `4`, then `(a / b) = -(b / a)`. -/
theorem jacobi_sym_quadratic_reciprocity_three_mod_four
  {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
  [a | b]ⱼ = - [b | a]ⱼ :=
let nop := @neg_one_pow_div_two_of_three_mod_four in begin
  rw [jacobi_sym_quadratic_reciprocity, pow_mul, nop ha, nop hb, neg_one_mul];
  rwa [odd_iff, odd_of_mod_four_eq_three],
end

/-- The Jacobi symbol `(a / b)` depends only on `b` mod `4*a` (version for `a : ℕ`). -/
lemma jacobi_sym_mod_right' (a : ℕ) {b : ℕ} (hb : odd b) : [a | b]ⱼ = [a | b % (4 * a)]ⱼ :=
begin
  cases eq_or_ne a 0 with ha₀ ha₀,
  { -- trivial case: `a = 0`
    rw [ha₀, mul_zero, mod_zero], },
  have hb' : odd (b % (4 * a)) :=
  odd_mod_of_odd hb (even.mul_right (by norm_num) _),
  have ha : ∃ e a' : ℕ, odd a' ∧ a = 2 ^ e * a',
  { let P : ℕ → Prop := λ n, n ≠ 0 → ∃ e n' : ℕ, odd n' ∧ n = 2 ^ e * n',
    have hp : ∀ (p : ℕ), p.prime → P p,
    { intros p pp _,
      cases pp.eq_two_or_odd' with hp₂ hp₂,
      { exact ⟨1, 1, odd_one, by rw [hp₂, pow_one, mul_one]⟩, },
      { exact ⟨0, p, hp₂, by rw [pow_zero, one_mul]⟩, } },
    have hmul : ∀ (m n : ℕ), P m → P n → P (m * n),
    { intros m n hm hn hmn,
      rcases hm (left_ne_zero_of_mul hmn) with ⟨em, m', hmo, hmm⟩,
      rcases hn (right_ne_zero_of_mul hmn) with ⟨en, n', hno, hnn⟩,
      refine ⟨em + en, m' * n', odd_mul.mpr ⟨hmo, hno⟩, _⟩,
      rw [hmm, hnn, pow_add, mul_mul_mul_comm], },
    exact rec_on_mul (λ hf, false.rec _ (hf rfl)) (λ _, ⟨0, 1, odd_one, by rw [pow_zero, mul_one]⟩)
                     hp hmul a ha₀, },
  rcases ha with ⟨e, a', ⟨ha₁, ha₂⟩⟩,
  nth_rewrite 1 [ha₂], nth_rewrite 0 [ha₂],
  rw [nat.cast_mul, jacobi_sym_mul_left, jacobi_sym_mul_left,
      jacobi_sym_quadratic_reciprocity' ha₁ hb, jacobi_sym_quadratic_reciprocity' ha₁ hb',
      nat.cast_pow, jacobi_sym_pow_left, jacobi_sym_pow_left,
      (by norm_cast : ((2 : ℕ) : ℤ) = 2), jacobi_sym_two hb, jacobi_sym_two hb'],
  have H : qr_sign b a' * [b | a']ⱼ = qr_sign (b % (4 * a)) a' * [b % (4 * a) | a']ⱼ,
  { simp_rw [qr_sign],
    have ha' : (a' : ℤ) ∣ 4 * a,
    { rw [ha₂, nat.cast_mul, ← mul_assoc],
      exact dvd_mul_left a' _, },
    rw [χ₄_nat_mod_four, χ₄_nat_mod_four (b % (4 * a)), mod_mod_of_dvd b (dvd_mul_right 4 a),
        jacobi_sym_mod_left b, jacobi_sym_mod_left (b % (4 * a)), int.mod_mod_of_dvd b ha'], },
  cases eq_or_ne e 0 with he he,
  { rw [he, pow_zero, pow_zero, one_mul, one_mul],
    exact H, },
  { have he' : e = 1 + (e - 1) := (nat.add_sub_of_le (nat.pos_of_ne_zero he)).symm,
    have h2 : 8 ∣ 4 * a,
    { rw [ha₂, he', pow_add, pow_one, ← mul_assoc, ← mul_assoc, (by norm_num : 4 * 2 = 8),
          mul_assoc],
      exact dvd_mul_right 8 _, },
    rw [H, χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b h2],
    refl, }
end

/-- The Jacobi symbol `(a / b)` depends only on `b` mod `4*a`. -/
lemma jacobi_sym_mod_right (a : ℤ) {b : ℕ} (hb : odd b) : [a | b]ⱼ = [a | b % (4 * a.nat_abs)]ⱼ :=
begin
  cases int.nat_abs_eq a with ha ha; nth_rewrite 1 [ha]; nth_rewrite 0 [ha],
  { -- `a = a.nat_abs`
    exact jacobi_sym_mod_right' a.nat_abs hb, },
  { -- `a = - a.nat_abs`
    have hb' : odd (b % (4 * a.nat_abs)) :=
    odd_mod_of_odd hb (even.mul_right (by norm_num) _),
    rw [jacobi_sym_neg _ hb, jacobi_sym_neg _ hb', jacobi_sym_mod_right' _ hb, χ₄_nat_mod_four,
        χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)], }
end

end jacobi

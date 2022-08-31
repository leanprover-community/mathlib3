/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.quadratic_reciprocity

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobi_sym a b` for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `zmod.legendre_sym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `nat.factors`. Since `nat.factors 0 = []`,
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

## Tags
Jacobi symbol, quadratic reciprocity
-/

/-!
### Some helpful lemmas

Once the dust has settled, these will be moved to the appropriate files.
-/

section nat

open nat

-- The following five lemmas should probably go to `data.nat.parity`, perhaps at the end.
/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
lemma odd.mod_even_iff {n a : ℕ} (ha : even a) : odd (n % a) ↔ odd n :=
((even_sub' $ mod_le n a).mp $ even_iff_two_dvd.mpr $ (even_iff_two_dvd.mp ha).trans $
   dvd_sub_mod n).symm

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
lemma even.mod_even_iff {n a : ℕ} (ha : even a) : even (n % a) ↔ even n :=
((even_sub $ mod_le n a).mp $ even_iff_two_dvd.mpr $ (even_iff_two_dvd.mp ha).trans $
   dvd_sub_mod n).symm

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
lemma odd.mod_even {n a : ℕ} (hn : odd n) (ha : even a) : odd (n % a) :=
(odd.mod_even_iff ha).mpr hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
lemma even.mod_even {n a : ℕ} (hn : even n) (ha : even a) : even (n % a) :=
(even.mod_even_iff ha).mpr hn

/-- `2` is not a prime factor of an odd natural number. -/
lemma odd.factors_ne_two {n p : ℕ} (hn : odd n) (hp : p ∈ n.factors) : p ≠ 2 :=
by { rintro rfl, exact two_dvd_ne_zero.mpr (odd_iff.mp hn) (dvd_of_mem_factors hp) }

-- The following lemma should probably go to `data.nat.prime`,
-- perhaps directly after `le_of_mem_factors`.
/-- If `a` is a nonzero natural number, then there are natural numbers `e` and `a'`
such that `a = 2^e * a'` and `a'` is odd. -/
lemma nat.two_pow_mul_odd {a : ℕ} (ha : a ≠ 0) : ∃ e a' : ℕ, odd a' ∧ a = 2 ^ e * a' :=
⟨a.factorization 2, ord_compl[2] a,
 odd_iff.mpr $ two_dvd_ne_zero.mp $ not_dvd_ord_compl prime_two ha,
 (ord_proj_mul_ord_compl_eq_self a 2).symm⟩

end nat

namespace int

-- The following four lemmas should probably go to `ring_theory.int.basic`
-- after `int.gcd_eq_one_iff_coprime`.
/-- If `gcd a (m * n) ≠ 1`, then `gcd a m ≠ 1` or `gcd a n ≠ 1`. -/
lemma gcd_ne_one_iff_gcd_mul_right_ne_one {a : ℤ} {m n : ℕ} :
  a.gcd (m * n) ≠ 1 ↔ a.gcd m ≠ 1 ∨ a.gcd n ≠ 1 :=
by simp only [gcd_eq_one_iff_coprime, ← not_and_distrib, not_iff_not, is_coprime.mul_right_iff]

/-- If `gcd a (m * n) = 1`, then `gcd a m = 1`. -/
lemma gcd_eq_one_of_gcd_mul_right_eq_one_left {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
  a.gcd m = 1 :=
nat.dvd_one.mp $ trans_rel_left _ (gcd_dvd_gcd_mul_right_right a m n) h

/-- If `gcd a (m * n) = 1`, then `gcd a n = 1`. -/
lemma gcd_eq_one_of_gcd_mul_right_eq_one_right {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
  a.gcd n = 1 :=
nat.dvd_one.mp $ trans_rel_left _ (gcd_dvd_gcd_mul_left_right a n m) h

-- Where should this go?
/-- The set `{0, 1, -1}` as a submonoid of the integers -/
def sign_submonoid : submonoid ℤ :=
⟨({0, 1, -1} : set ℤ),
   by rintro _ _ (rfl | rfl | (rfl : _ = _)) (rfl | rfl | (rfl : _ = _)); dec_trivial,
   or.inr (or.inl rfl)⟩

end int

namespace zmod

-- Where should these three lemmas go?
-- In `data.zmod.basic`, `int.gcd_eq_one_iff_coprime` is not visible,
-- and in `ring_theory.int.basic`, `zmod.int_coe_mod_eq_zero_iff_dvd` is not visible.
-- `data.zmod.quotient` is a file that imports both, but has a different topic...
/-- If `p` is a prime and `a` is an integer, then `a : zmod p` is zero if and only if
`gcd a p ≠ 1`. -/
lemma eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : fact p.prime] : (a : zmod p) = 0 ↔ a.gcd p ≠ 1 :=
by rw [ne, int.gcd_comm, int.gcd_eq_one_iff_coprime,
       (nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, not_not, int_coe_zmod_eq_zero_iff_dvd]

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : zmod p` is nonzero. -/
lemma ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p = 1) :
  (a : zmod p) ≠ 0 :=
mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (not_not.mpr h)

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : zmod p` is zero. -/
lemma eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p ≠ 1) :
  (a : zmod p) = 0 :=
(@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

end zmod

namespace list

-- This should probably go to `data.list.basic` at the end of the `pmap` section
lemma pmap_append {α β : Type*} {p : α → Prop} (f : Π (a : α), p a → β) (l₁ l₂ : list α)
  (h : ∀ (a : α), a ∈ l₁ ++ l₂ → p a) :
  (l₁ ++ l₂).pmap f h = l₁.pmap f (λ a ha, h a (mem_append_left l₂ ha)) ++
                        l₂.pmap f (λ a ha, h a (mem_append_right l₁ ha)) :=
begin
  induction l₁ with _ _ ih,
  { refl, },
  { dsimp only [pmap, cons_append],
    rw ih, }
end

end list

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
-- Since we need the fact that the factors are prime, we use `list.pmap`.
def jacobi_sym (a : ℤ) (b : ℕ) : ℤ :=
(b.factors.pmap (λ p pp, @legendre_sym p ⟨pp⟩ a) (λ p pf, prime_of_mem_factors pf)).prod

-- Notation for the Jacobi symbol.
localized "notation `[` a ` | ` b `]ⱼ` := jacobi_sym a b" in number_theory_symbols

/-!
### Properties of the Jacobi symbol
-/

open_locale number_theory_symbols

/-- The Jacobi symbol `(a / 0)` has the value `1`. -/
@[simp] lemma jacobi_sym_zero_right (a : ℤ) : [a | 0]ⱼ = 1 :=
by simp only [jacobi_sym, factors_zero, list.prod_nil, list.pmap]

/-- The Jacobi symbol `(a / 1)` has the value `1`. -/
@[simp] lemma jacobi_sym_one_right (a : ℤ) : [a | 1]ⱼ = 1 :=
by simp only [jacobi_sym, factors_one, list.prod_nil, list.pmap]

/-- The Legendre symbol `(a / p)` with an integer `a` and a prime number `p`
is the same as the Jaocbi symbol `(a / p)`. -/
lemma legendre_sym.to_jacobi_sym {p : ℕ} [fp : fact p.prime] {a : ℤ} :
  legendre_sym p a = [a | p]ⱼ :=
by simp only [jacobi_sym, factors_prime fp.1, list.prod_cons, list.prod_nil, mul_one, list.pmap]

/-- The Jacobi symbol is multiplicative in its second argument. -/
lemma jacobi_sym_mul_right (a : ℤ) (b₁ b₂ : ℕ) [ne_zero b₁] [ne_zero b₂] :
  [a | b₁ * b₂]ⱼ = [a | b₁]ⱼ * [a | b₂]ⱼ :=
begin
  rw [jacobi_sym, ((perm_factors_mul (ne_zero.ne b₁) (ne_zero.ne b₂)).pmap _).prod_eq,
      list.pmap_append, list.prod_append],
  exacts [rfl, λ p hp, (list.mem_append.mp hp).elim prime_of_mem_factors prime_of_mem_factors],
end

/-- The Jacobi symbol takes only the values `0`, `1` and `1`. -/
lemma jacobi_sym_trichotomy (a : ℤ) (b : ℕ) : [a | b]ⱼ = 0 ∨ [a | b]ⱼ = 1 ∨ [a | b]ⱼ = -1 :=
submonoid.list_prod_mem int.sign_submonoid
begin
  intros _ ha',
  rcases list.mem_pmap.mp ha' with ⟨p, hp, rfl⟩,
  haveI : fact p.prime := ⟨prime_of_mem_factors hp⟩,
  exact quadratic_char_is_quadratic (zmod p) a,
end

/-- The Jacobi symbol `(1 / b)` has the value `1`. -/
@[simp] lemma jacobi_sym_one_left (b : ℕ) : [1 | b]ⱼ = 1 :=
list.prod_eq_one (λ z hz, let ⟨p, hp, he⟩ := list.mem_pmap.1 hz in by rw [← he, legendre_sym_one])

/-- The Jacobi symbol is multiplicative in its first argument. -/
lemma jacobi_sym_mul_left (a₁ a₂ : ℤ) (b : ℕ) : [a₁ * a₂ | b]ⱼ = [a₁ | b]ⱼ * [a₂ | b]ⱼ :=
by { simp_rw [jacobi_sym, list.pmap_eq_map_attach, legendre_sym_mul], exact list.prod_map_mul }

/-- The Jacobi symbol `(a / b)` vanishes iff `a` and `b` are not coprime (assuming `b ≠ 0`). -/
lemma jacobi_sym_eq_zero_iff_not_coprime {a : ℤ} {b : ℕ} [ne_zero b] :
  [a | b]ⱼ = 0 ↔ a.gcd b ≠ 1 :=
list.prod_eq_zero_iff.trans begin
  rw [list.mem_pmap, int.gcd_eq_nat_abs, ne, prime.not_coprime_iff_dvd],
  simp_rw [legendre_sym_eq_zero_iff, int_coe_zmod_eq_zero_iff_dvd, mem_factors (ne_zero.ne b),
    ← int.coe_nat_dvd_left, int.coe_nat_dvd, exists_prop, and_assoc, and_comm],
end

/-- The Jacobi symbol `(a / b)` is nonzero when `a` and `b` are coprime. -/
lemma jacobi_sym_ne_zero {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a | b]ⱼ ≠ 0 :=
begin
  casesI eq_zero_or_ne_zero b with hb,
  rw [hb, jacobi_sym_zero_right],
  { exact one_ne_zero },
  { contrapose! h, exact jacobi_sym_eq_zero_iff_not_coprime.1 h },
end

/-- The Jacobi symbol `(a / b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
lemma jacobi_sym_eq_zero_iff {a : ℤ} {b : ℕ} : [a | b]ⱼ = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
⟨λ h, begin
  casesI eq_or_ne b 0 with hb hb,
  { rw [hb, jacobi_sym_zero_right] at h, cases h },
  exact ⟨hb, mt jacobi_sym_ne_zero $ not_not.2 h⟩,
end, λ ⟨hb, h⟩, by { rw ← ne_zero_iff at hb, exactI jacobi_sym_eq_zero_iff_not_coprime.2 h }⟩

/-- The Jacobi symbol `(0 / b)` vanishes when `b > 1`. -/
lemma jacobi_sym_zero_left {b : ℕ} (hb : 1 < b) : [0 | b]ⱼ = 0 :=
(@jacobi_sym_eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr $
  by { rw [int.gcd_zero_left, int.nat_abs_of_nat], exact hb.ne' }

/-- The Jacobi symbol `(a / b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
lemma jacobi_sym_eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) :
  [a | b]ⱼ = 1 ∨ [a | b]ⱼ = -1 :=
(jacobi_sym_trichotomy a b).resolve_left $ jacobi_sym_ne_zero h

/-- We have that `(a^e / b) = (a / b)^e` for the Jacobi symbol. -/
lemma jacobi_sym_pow_left (a : ℤ) (e b : ℕ) : [a ^ e | b]ⱼ = [a | b]ⱼ ^ e :=
nat.rec_on e (by rw [pow_zero, pow_zero, jacobi_sym_one_left]) $
  λ _ ih, by rw [pow_succ, pow_succ, jacobi_sym_mul_left, ih]

/-- We have that `(a / b^e) = (a / b)^e` for the Jacobi symbol. -/
lemma jacobi_sym_pow_right (a : ℤ) (b e : ℕ) : [a | b ^ e]ⱼ = [a | b]ⱼ ^ e :=
begin
  induction e with e ih,
  { rw [pow_zero, pow_zero, jacobi_sym_one_right], },
  { casesI eq_zero_or_ne_zero b with hb,
    { rw [hb, zero_pow (succ_pos e), jacobi_sym_zero_right, one_pow], },
    { rw [pow_succ, pow_succ, jacobi_sym_mul_right, ih], } }
end

/-- The square of the Jacobi symbol `(a / b)` is `1` when `a` and `b` are coprime. -/
lemma jacobi_sym_sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a | b]ⱼ ^ 2 = 1 :=
by cases jacobi_sym_eq_one_or_neg_one h with h₁ h₁; rw h₁; refl

/-- The Jacobi symbol `(a^2 / b)` is `1` when `a` and `b` are coprime. -/
lemma jacobi_sym_sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a ^ 2 | b]ⱼ = 1 :=
by rw [jacobi_sym_pow_left, jacobi_sym_sq_one h]

/-- The Jacobi symbol `(a / b)` depends only on `a` mod `b`. -/
lemma jacobi_sym_mod_left (a : ℤ) (b : ℕ) : [a | b]ⱼ = [a % b | b]ⱼ :=
congr_arg list.prod $ list.pmap_congr _ begin
  rintro p hp _ _,
  conv_rhs { rw [legendre_sym_mod, int.mod_mod_of_dvd _
    (int.coe_nat_dvd.2 $ dvd_of_mem_factors hp), ← legendre_sym_mod] },
end

/-- The Jacobi symbol `(a / b)` depends only on `a` mod `b`. -/
lemma jacobi_sym_mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : [a₁ | b]ⱼ = [a₂ | b]ⱼ :=
by rw [jacobi_sym_mod_left, h, ← jacobi_sym_mod_left]

/-- If the Jacobi symbol `(a / b)` is `-1`, then `a` is not a square modulo `b`. -/
lemma nonsquare_of_jacobi_sym_eq_neg_one {a : ℤ} {b : ℕ} (h : [a | b]ⱼ = -1) : ¬ is_square (a : zmod b) :=
λ ⟨r, ha⟩, begin
  rw [← r.coe_val_min_abs, ← int.cast_mul, int_coe_eq_int_coe_iff', ← sq] at ha,
  apply (by norm_num : ¬ (0 : ℤ) ≤ -1),
  rw [← h, jacobi_sym_mod_left, ha, ← jacobi_sym_mod_left, jacobi_sym_pow_left],
  apply sq_nonneg,
end

/-- If `p` is prime, then the Jacobi symbol `(a / p)` is `-1` iff `a` is not a square modulo `p`. -/
lemma nonsquare_iff_jacobi_sym_eq_neg_one {a : ℤ} {p : ℕ} [fact p.prime] :
  [a | p]ⱼ = -1 ↔ ¬ is_square (a : zmod p) :=
by { rw [← legendre_sym.to_jacobi_sym], exact legendre_sym_eq_neg_one_iff p }

/-!
### Values at `-1`, `2` and `-2`
-/

/-- If `χ` is a multiplicative function such that `(a / p) = χ p` for all odd primes `p`,
then the Jacobi symbol `(a / b)` equals `χ b` for all odd natural numbers `b`. -/
lemma jacobi_sym_value (a : ℤ) {R : Type*} [comm_semiring R] (χ : R →* ℤ)
  (hp : ∀ (p : ℕ) (pp : p.prime) (h2 : p ≠ 2), @legendre_sym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : odd b) :
  [a | b]ⱼ = χ b :=
begin
  conv_rhs { rw [← prod_factors hb.pos.ne', cast_list_prod, χ.map_list_prod] },
  rw [jacobi_sym, list.map_map, ← list.pmap_eq_map nat.prime _ _ (λ _, prime_of_mem_factors)],
  congr' 1, apply list.pmap_congr,
  exact λ p h pp _, hp p pp (hb.factors_ne_two h),
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
  rw [qr_sign, pow_mul, ← χ₄_eq_neg_one_pow (odd_iff.mp hm)],
  cases odd_mod_four_iff.mp (odd_iff.mp hm) with h h,
  { rw [χ₄_nat_one_mod_four h, jacobi_sym_one_left, one_pow], },
  { rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobi_sym_neg_one hn], }
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
by refine ⟨λ h', let h := h'.symm in _, λ h, _⟩;
   rw [h, ← mul_assoc, ← pow_two, qr_sign_sq_eq_one hm hn, one_mul]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma jacobi_sym_quadratic_reciprocity' {a b : ℕ} (ha : odd a) (hb : odd b) :
  [a | b]ⱼ = qr_sign b a * [b | a]ⱼ :=
begin
  -- define the right hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : ℕ →  ℕ →* ℤ := λ a,
  { to_fun := λ x, qr_sign x a * [x | a]ⱼ,
    map_one' := by { convert ← mul_one _, symmetry, all_goals { apply jacobi_sym_one_left } },
    map_mul' := λ x y, by rw [qr_sign_mul_left, nat.cast_mul, jacobi_sym_mul_left,
                              mul_mul_mul_comm] },
  have rhs_apply : ∀ (a b : ℕ), rhs a b = qr_sign b a * [b | a]ⱼ := λ a b, rfl,
  refine jacobi_sym_value a (rhs a) (λ p pp hp, eq.symm _) hb,
  have hpo := pp.eq_two_or_odd'.resolve_left hp,
  rw [@legendre_sym.to_jacobi_sym p ⟨pp⟩, rhs_apply, nat.cast_id,
      qr_sign_eq_iff_eq hpo ha, qr_sign_symm hpo ha],
  refine jacobi_sym_value p (rhs p) (λ q pq hq, _) ha,
  have hqo := pq.eq_two_or_odd'.resolve_left hq,
  rw [rhs_apply, nat.cast_id, ← @legendre_sym.to_jacobi_sym p ⟨pp⟩, qr_sign_symm hqo hpo,
      qr_sign_neg_one_pow hpo hqo, @quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq],
end

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma jacobi_sym_quadratic_reciprocity {a b : ℕ} (ha : odd a) (hb : odd b) :
  [a | b]ⱼ = (-1) ^ ((a / 2) * (b / 2)) * [b | a]ⱼ :=
by rw [← qr_sign_neg_one_pow ha hb, qr_sign_symm ha hb, jacobi_sym_quadratic_reciprocity' ha hb]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a % 4 = 1` and `b` odd, then `(a / b) = (b / a)`. -/
theorem jacobi_sym_quadratic_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : odd b) :
  [a | b]ⱼ = [b | a]ⱼ :=
by rw [jacobi_sym_quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb,
       pow_mul, neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]

/-- The Law of Quadratic Reciprocityfor the Jacobi symbol: if `a` and `b` are natural numbers
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
  rcases eq_or_ne a 0 with rfl | ha₀,
  { rw [mul_zero, mod_zero], },
  have hb' : odd (b % (4 * a)) := hb.mod_even (even.mul_right (by norm_num) _),
  rcases two_pow_mul_odd ha₀ with ⟨e, a', ha₁, ha₂⟩,
  nth_rewrite 1 [ha₂], nth_rewrite 0 [ha₂],
  rw [nat.cast_mul, jacobi_sym_mul_left, jacobi_sym_mul_left,
      jacobi_sym_quadratic_reciprocity' ha₁ hb, jacobi_sym_quadratic_reciprocity' ha₁ hb',
      nat.cast_pow, jacobi_sym_pow_left, jacobi_sym_pow_left,
      (show ((2 : ℕ) : ℤ) = 2, by refl), jacobi_sym_two hb, jacobi_sym_two hb'],
  congr' 1, swap, congr' 1,
  { simp_rw [qr_sign],
    rw [χ₄_nat_mod_four, χ₄_nat_mod_four (b % (4 * a)), mod_mod_of_dvd b (dvd_mul_right 4 a) ] },
  { rw [jacobi_sym_mod_left ↑(b % _), jacobi_sym_mod_left b, int.coe_nat_mod,
        int.mod_mod_of_dvd b],
    simp only [ha₂, nat.cast_mul, ← mul_assoc],
    exact dvd_mul_left a' _, },
  cases e, { refl },
  { rw [χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b],
    use 2 ^ e * a', rw [ha₂, pow_succ], ring, }
end

/-- The Jacobi symbol `(a / b)` depends only on `b` mod `4*a`. -/
lemma jacobi_sym_mod_right (a : ℤ) {b : ℕ} (hb : odd b) : [a | b]ⱼ = [a | b % (4 * a.nat_abs)]ⱼ :=
begin
  cases int.nat_abs_eq a with ha ha; nth_rewrite 1 [ha]; nth_rewrite 0 [ha],
  { -- `a = a.nat_abs`
    exact jacobi_sym_mod_right' a.nat_abs hb, },
  { -- `a = - a.nat_abs`
    have hb' : odd (b % (4 * a.nat_abs)) := hb.mod_even (even.mul_right (by norm_num) _),
    rw [jacobi_sym_neg _ hb, jacobi_sym_neg _ hb', jacobi_sym_mod_right' _ hb, χ₄_nat_mod_four,
        χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)], }
end

end jacobi

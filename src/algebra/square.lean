/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import ring_theory.int.basic

/-!
# Square elements of monoids
An element `x` of a monoid is a square when there is another element `y` such that `y * y = x`.

## Main Definitions
 - `square r` indicates that `∃ s, s * s = r`.

## Main Results
 - `nat.square_iff_factorization_even`: `x` is a `square` iff every entry in its factorization
   is even
 - `nat.square_mul`: Being `square` is multiplicative

## TODO

There are many more facts about squares that generalize to arbitrary `unique_factorization_monoid`s.
The should eventually be added.

## Tags
square, squarefree, multiplicity

-/

variables {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def square [monoid R] (r : R) : Prop := ∃ x : R, x * x = r

@[simp]
lemma square_one [comm_monoid R] : square (1 : R) := ⟨1, mul_one 1⟩

@[simp]
lemma square_zero [monoid_with_zero R] : square (0 : R) := ⟨0, mul_zero 0⟩

@[simp]
lemma irreducible.not_square [comm_monoid R] {x : R} (h : irreducible x) :
  ¬square x :=
begin
  rintros ⟨y, hy⟩,
  rcases h.is_unit_or_is_unit hy.symm with hu | hu;
  rw ← hy at h;
  exact h.not_unit (hu.mul hu)
end

@[simp]
lemma prime.not_square [cancel_comm_monoid_with_zero R] {x : R} (h : prime x) :
  ¬square x := h.irreducible.not_square

/-- The product of squares is a square. For a partial converse, see `nat.square_mul` -/
lemma square_mul_of_square_of_square {R : Type*} [comm_monoid R] {m n : R} :
  square m → square n → square (m * n) :=
begin
  rintros ⟨c, hc⟩,
  rintros ⟨d, hd⟩,
  use (c * d),
  have : c * d * (c * d) = (c * c) * (d * d),
  { rw mul_assoc,
    conv in (d * (c * d)) { rw [mul_comm, mul_assoc], },
    rw ←mul_assoc, },
  rw [this, hc, hd],
end

section factorization

namespace nat

instance : decidable_pred (square : ℕ → Prop)
| n := decidable_of_iff' _ (nat.exists_mul_self n)

lemma square_iff_factorization_even {m : ℕ} :
square m ↔ ∀ (p : ℕ), even (m.factorization p) :=
begin
  by_cases hm_zero : m = 0,
  { simp only [hm_zero, square_zero, factorization_zero, finsupp.coe_zero,
      pi.zero_apply, forall_const, true_iff],
    use 0,
    exact mul_zero 2, },
  { split,
    { rintros ⟨c, hc⟩,
      by_cases hc' : c = 0,
      { rw [hc', mul_zero] at hc,
        rw ←hc,
        simp only [factorization_zero, finsupp.coe_zero, pi.zero_apply, forall_const],
        use 0,
        exact mul_zero 2, },
      { intros p,
        rw [←hc, nat.factorization_mul hc' hc', finsupp.coe_add, ←two_mul],
        simp [even], }, },
    { intros hp,
      use m.factorization.prod (λ p i, p ^ (i / 2)),
      rw ← finsupp.prod_mul,
      conv { to_rhs, rw ← nat.factorization_prod_pow_eq_self hm_zero,},
      apply finsupp.prod_congr,
      intros x hx,
      rcases hp x with ⟨c, hc⟩,
      rw [←pow_add, ←two_mul, hc],
      congr,
      simp, }, },
end

/-- The property of being a square is multiplicative. The ← direction can be generalized
to an arbitrary commutative monoid. See `square_mul_of_square_of_square`. Similarly,
this lemma could be generalized to an arbitrary unique factorization domain, but we make use
of `nat.factorization` in this proof. -/
lemma square_mul {m n : ℕ} (hmn : m.coprime n) :
  square (m * n) ↔ square m ∧ square n :=
begin
  split,
  { rw [square_iff_factorization_even, square_iff_factorization_even],
    rw square_iff_factorization_even,
    intros hmn',
    split,
    { intros p,
      by_cases hp : p ∈ m.factors,
      { rw ← factorization_eq_of_coprime_left hmn hp, exact hmn' p, },
      { rw [←nat.factors_count_eq, list.count_eq_zero_of_not_mem hp],
        use zero,
        exact mul_zero 2, }, },
    { intros p,
      by_cases hp : p ∈ n.factors,
      { rw ← factorization_eq_of_coprime_right hmn hp, exact hmn' p, },
      { rw [←nat.factors_count_eq, list.count_eq_zero_of_not_mem hp],
        use zero,
        exact mul_zero 2, }, }, },
  { rintros ⟨hm, hn⟩, exact square_mul_of_square_of_square hm hn, },
end

lemma square_prime_pow_iff_pow_even : ∀ (p i : ℕ), nat.prime p → (square (p ^ i) ↔ even i) :=
begin
  intros p i hp,
  split,
  { rintros ⟨s, hs⟩,
    have : s ∣ p ^ i,
      calc s ∣ s * s : dvd_mul_left s s
        ... = p ^ i : hs,
    rw nat.dvd_prime_pow hp at this,
    rcases this with ⟨k, hk, s_eq⟩,
    rw [s_eq, ←pow_add] at hs,
    have aa : (p ^ (k + k)).factorization p = k + k, { simp [hp.factorization_pow], },
    have bb : (p ^ i).factorization p = i, { simp [hp.factorization_pow], },
    have : i = k + k, { rw [←aa, ←bb, hs], },
    rw this,
    use k,
    exact (two_mul k).symm, },
  { rintros ⟨k, hk⟩,
    use p ^ k,
    rw [hk, pow_mul, pow_two, mul_pow], },
end

/-- If `x` is a square, return its square root. Else, return 0. -/
def sqrt0 (x : ℕ) := ite (square x) (sqrt x) 0

lemma sqrt0_zero : sqrt0 0 = 0 := by simp only [sqrt0, square_zero, if_true, sqrt_zero]

lemma sqrt0_one : sqrt0 1 = 1 := by simp only [sqrt0, square_one, if_true, sqrt_one]

lemma sqrt0_prime {p : ℕ} (hp : nat.prime p) : sqrt0 p = 0 :=
begin
  simp only [sqrt0, ite_eq_right_iff],
  intros p,
  exfalso,
  exact (nat.prime_iff.mp hp).not_square p,
end

lemma sqrt0_eq {n : ℕ} : sqrt0 (n * n) = n :=
begin
  have : square (n * n), use n,
  simp only [sqrt0, sqrt_eq, this, if_true],
end

/-- `sqrt0` is multiplicative. Note that coprimality is necessary. -/
lemma sqrt0_mul {a b : ℕ} (hab : a.coprime b) : sqrt0 (a * b) = (sqrt0 a) * (sqrt0 b) :=
begin
  by_cases ha : square a,
  { by_cases hb : square b,
    { have : square (a * b), exact square_mul_of_square_of_square ha hb,
      simp only [sqrt0, ha, hb, this, if_true],
      cases ha with a' ha',
      cases hb with b' hb',
      have : a' * a' * (b' * b') = (a' * b') * (a' * b'), ring,
      rw [←ha', ←hb', this],
      rw [sqrt_eq, sqrt_eq, sqrt_eq], },
    { have : ¬(square a ∧ square b), simp only [hb, and_false, not_false_iff],
      simp [sqrt0, ha, hb, (square_mul hab).not.mpr this], }, },
  { have : ¬(square a ∧ square b), simp only [ha, false_and, not_false_iff],
    simp [sqrt0, ha, (square_mul hab).not.mpr this], },
end

end nat

end factorization

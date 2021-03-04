/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.abel
import data.polynomial.eval

/-!
# The rising and falling factorial functions

We define and prove some basic relations about
`rising_factorial x n = x * (x+1) * ... * (x + n - 1)`
which is also known as the Pochhammer function
and its cousin
`falling_factorial x n = x * (x-1) * ... * (x - (n-1))`.

## Implementation

In a commutative ring we have `rising_factorial r n = falling_factorial (r + n - 1) n`,
but for the sake of (perhaps needless?) generality
we give separate inductive definitions in a `[semiring R]`,
additionally requiring `[has_sub R]` for `falling_factorial`.
A few of the theorems require separate proofs assuming either `[ring R]` or `R = ℕ`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
* Defining Bernstein polynomials (e.g. as one way to prove Weierstrass' theorem).
-/

variables (S : Type*) [semiring S]

open polynomial

noncomputable def pochhammer : ℕ → polynomial S
| 0 := 1
| (n+1) := X * (pochhammer n).comp(X + 1)

@[simp] lemma pochhammer_zero : pochhammer S 0 = 1 := rfl
@[simp] lemma pochhammer_one : pochhammer S 1 = X := by simp [pochhammer]
@[simp] lemma pochhammer_succ_left (n : ℕ) : pochhammer S (n+1) = X * (pochhammer S n).comp (X+1) :=
by { dsimp [pochhammer], refl, }

section
variables {S} {T : Type*} [semiring T]
@[simp] lemma pochhammer_map (f : S →+* T) (n : ℕ): (pochhammer S n).map f = pochhammer T n :=
begin
  induction n with n ih,
  { simp, },
  { simp [ih, map_comp], },
end


@[simp] lemma pochhammer_succ_right (n : ℕ) : pochhammer ℕ (n+1) = pochhammer ℕ n * (X + n) :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs {
    rw [pochhammer_succ_left, ih, mul_comp, ←mul_assoc, ←pochhammer_succ_left, add_comp, X_comp,
      nat_cast_comp], },
    simp?, }
end


variables {R : Type*}

section
variables [semiring R]

/--
The rising factorial function: `rising_factorial x n = x * (x+1) * ... * (x + n - 1)`.

It is also sometimes called the Pochhammer polynomial, or the upper factorial.
Notations in the mathematics literature vary extensively.
-/
def rising_factorial : R → ℕ → R
| r 0 := 1
| r (n+1) := r * rising_factorial (r+1) n

@[simp]
lemma rising_factorial_zero {r : R} : rising_factorial r 0 = 1 := rfl
@[simp]
lemma rising_factorial_one {r : R} : rising_factorial r 1 = r := by simp [rising_factorial]

lemma rising_factorial_eq_mul_left {r : R} {n : ℕ} :
  rising_factorial r (n + 1) = r * rising_factorial (r+1) n := rfl

lemma rising_factorial_eq_mul_right {r : R} {n : ℕ} :
  rising_factorial r (n + 1) = rising_factorial r n * (r + n) :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { rw [rising_factorial, ih, rising_factorial, nat.succ_eq_add_one],
    push_cast,
    rw [mul_assoc, add_comm (n : R) 1, add_assoc], }
end

lemma rising_factorial_mul_rising_factorial {r : R} {n m : ℕ} :
  rising_factorial r n * rising_factorial (r + n) m = rising_factorial r (n + m) :=
begin
  induction m with m ih,
  { simp, },
  { rw [rising_factorial_eq_mul_right, ←mul_assoc, ih, nat.add_succ, rising_factorial_eq_mul_right],
    push_cast,
    rw [add_assoc], }
end
end

section
variables [semiring R] [has_sub R]

/--
The falling factorial function: `falling_factorial x n = x * (x-1) * ... * (x - (n - 1))`.
-/
def falling_factorial : R → ℕ → R
| r 0 := 1
| r (n+1) := r * falling_factorial (r-1) n

@[simp]
lemma falling_factorial_zero {r : R} : falling_factorial r 0 = 1 := rfl
@[simp]
lemma falling_factorial_one {r : R} : falling_factorial r 1 = r := by simp [falling_factorial]

lemma falling_factorial_eq_mul_left {r : R} {n : ℕ} :
  falling_factorial r (n + 1) = r * falling_factorial (r-1) n := rfl
end

section
-- In fact, the lemmas in this section apply to `ℕ` as well:
-- they only use `n - 0 = n` and `n - m - k = n - (m + k)`.
-- Without a `[monus R]` typeclass, we just prove them separately below in the `nat` namespace.
variables [ring R]

lemma falling_factorial_eq_mul_right {r : R} {n : ℕ} :
  falling_factorial r (n + 1) = falling_factorial r n * (r - n) :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { rw [falling_factorial, ih, falling_factorial, nat.succ_eq_add_one],
    push_cast,
    rw [mul_assoc, add_comm (n : R) 1, ←sub_sub], }
end

lemma falling_factorial_mul_falling_factorial {r : R} {n m : ℕ} :
  falling_factorial r n * falling_factorial (r - n) m = falling_factorial r (n + m) :=
begin
  induction m with m ih,
  { simp, },
  { rw [falling_factorial_eq_mul_right, ←mul_assoc, ih, nat.add_succ,
      falling_factorial_eq_mul_right],
    push_cast,
    rw [sub_sub], }
end

end

namespace nat

section
variables [ring R]

@[norm_cast]
lemma falling_factorial_coe {r n : ℕ} :
  ((falling_factorial r n : ℕ) : R) = falling_factorial (r : R) n :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { simp only [falling_factorial, falling_factorial_eq_mul_left, nat.cast_mul],
    rw [ih],
    { by_cases w : r = 0,
      { subst w, simp, },
      { replace w : 0 < r := nat.pos_of_ne_zero w,
        push_cast [w], }, }, },
end

/-- We already have this theorem for `r : R` with `[ring R]`,
but need to prove it separately for `ℕ`.-/
lemma falling_factorial_eq_mul_right {r n : ℕ} :
  falling_factorial r (n + 1) = falling_factorial r n * (r - n) :=
begin
  -- We could prove this from the ring case by using the injectivity of `ℕ → ℤ`,
  -- but it involves casing on `n ≤ r`, so it's easier to just redo it from scratch.
  induction n with n ih generalizing r,
  { simp, },
  { rw [falling_factorial, ih, falling_factorial, succ_eq_add_one],
    rw [mul_assoc, add_comm n 1, ←nat.sub_sub], }
end

@[simp]
lemma falling_factorial_eq_factorial {n : ℕ} :
  falling_factorial n n = n.factorial :=
begin
  induction n with n ih,
  { simp, },
  { simp [falling_factorial_eq_mul_left, ih], }
end

/-- We already have this theorem for `r : R` with `[ring R]`,
but need to prove it separately for `ℕ`.-/
lemma falling_factorial_mul_falling_factorial {r n m : ℕ} :
  falling_factorial r n * falling_factorial (r - n) m = falling_factorial r (n + m) :=
begin
  induction m with m ih,
  { simp, },
  { rw [falling_factorial_eq_mul_right, ←mul_assoc, ih, add_succ,
      falling_factorial_eq_mul_right, nat.sub_sub], }
end

lemma falling_factorial_ne_zero {n m : ℕ} (h : n ≤ m) :
  falling_factorial m n ≠ 0 :=
begin
  intro w,
  have := @falling_factorial_mul_falling_factorial m n (m-n),
  rw [w, nat.add_sub_cancel' h, zero_mul, falling_factorial_eq_factorial] at this,
  exact ne_of_lt m.factorial_pos this,
end

end

end nat

section
variables [comm_ring R]

lemma rising_factorial_eq_falling_factorial {r : R} {n : ℕ} :
  rising_factorial r n = falling_factorial (r + n - 1) n :=
begin
  induction n with n ih generalizing r,
  { refl, },
  { rw [rising_factorial, falling_factorial_eq_mul_right, ih, mul_comm, nat.succ_eq_add_one],
    push_cast,
    congr' 2; abel, }
end

end

section
lemma rising_factorial_eq_factorial {n : ℕ} :
  rising_factorial 1 n = n.factorial :=
begin
  induction n with n ih,
  { refl, },
  { rw [rising_factorial_eq_mul_right, nat.factorial, ih, mul_comm, add_comm], push_cast, }
end

lemma factorial_mul_rising_factorial {r n : ℕ} :
  r.factorial * rising_factorial (r+1) n = (r + n).factorial :=
begin
  rw [←rising_factorial_eq_factorial, add_comm, ←rising_factorial_eq_factorial],
  convert rising_factorial_mul_rising_factorial,
  simp,
end

lemma rising_factorial_eq_factorial_div_factorial {r n : ℕ} :
  rising_factorial (r+1) n = (r + n).factorial / r.factorial :=
(nat.div_eq_of_eq_mul_right (nat.factorial_pos _) factorial_mul_rising_factorial.symm).symm

lemma rising_factorial_eq_choose_mul_factorial {r n : ℕ} :
  rising_factorial (r+1) n = (r + n).choose n * n.factorial :=
begin
  rw rising_factorial_eq_factorial_div_factorial,
  -- TODO we need a `clear_denominators` tactic!
  apply nat.div_eq_of_eq_mul_right (nat.factorial_pos _),
  rw [mul_comm],
  convert (nat.choose_mul_factorial_mul_factorial (nat.le_add_left n r)).symm,
  simp,
end

lemma choose_eq_rising_factorial_div_factorial {r n : ℕ} :
  (r + n).choose n = rising_factorial (r+1) n / n.factorial :=
begin
  symmetry,
  apply nat.div_eq_of_eq_mul_right (nat.factorial_pos _),
  rw [mul_comm, rising_factorial_eq_choose_mul_factorial],
end
end

namespace ring_hom

local attribute [simp] rising_factorial falling_factorial

variables {S : Type*}

section
variables [semiring R] [semiring S]

@[simp]
lemma map_rising_factorial (f : R →+* S) {r : R} {n : ℕ} :
  f (rising_factorial r n) = rising_factorial (f r) n :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { simp [ih], }
end

@[norm_cast]
lemma nat_coe_rising_factorial {r n : ℕ} :
  ((rising_factorial r n : ℕ) : R) = rising_factorial (r : R) n :=
by rw [←nat.coe_cast_ring_hom, map_rising_factorial]

end

section
variables [ring R] [ring S]

@[simp]
lemma map_falling_factorial (f : R →+* S) {r : R} {n : ℕ} :
  f (falling_factorial r n) = falling_factorial (f r) n :=
begin
  induction n with n ih generalizing r,
  { simp, },
  { simp [ih], }
end

@[norm_cast]
lemma int_coe_rising_factorial {r : ℤ} {n : ℕ} :
  ((rising_factorial r n : ℤ) : R) = rising_factorial (r : R) n :=
by rw [←int.coe_cast_ring_hom, map_rising_factorial]

@[norm_cast]
lemma int_coe_falling_factorial {r : ℤ} {n : ℕ} :
  ((falling_factorial r n : ℤ) : R) = falling_factorial (r : R) n :=
by rw [←int.coe_cast_ring_hom, map_falling_factorial]

end
end ring_hom

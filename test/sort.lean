import tactic.sort
import data.polynomial.degree

open polynomial tactic interactive
open_locale polynomial

variables {R : Type*} [semiring R] (f g h : R[X]) {r s t u : R}

<<<<<<< HEAD
example (s0 : s ≠ 0) (m n : ℕ) (mn : m < n) (m1 : 1 ≤ m) :
  (C r * X ^ m + (5 + C s * X ^ n) + m * X + 37 * X).nat_degree = n :=
begin
  -- move `C s * X ^ n` to the right, since it is the term with highest degree
  -- we also move `m * X` and `37 * X` to the left, to collect them in a single summand
  sort_summands [C s * X ^ n, ← ↑m * (X : R[X]), ← 37 * (X : R[X])],
  rw [← add_mul, nat_degree_add_eq_right_of_nat_degree_lt, nat_degree_C_mul_X_pow _ _ s0],
  rw [nat_degree_C_mul_X_pow _ _ s0],
  -- what is left has degree at most `m < n`, so let's inform Lean
  refine lt_of_le_of_lt _ mn,
  -- all summands are now of degree at most `m`, so we break the sum into pieces
  repeat { refine (nat_degree_add_le _ _).trans _,
    refine max_le _ _ };
    try { simp only [nat_degree_one, zero_le], done },
  -- we have now focused on the two "interesting" terms
  { convert (nat_degree_C_mul_X_pow_le (m + 37 : R) _).trans m1;
    simp only [map_add, C_eq_nat_cast, C_bit1, C_bit0, map_one, pow_one] },
  { exact nat_degree_C_mul_X_pow_le _ _ }
end

=======
>>>>>>> 6716bee7a655bb7d0d689bc1b577a8f5a6803106
example
  (hp : (monomial 1) u + (g + (monomial 5) 1) + 5 * X + ((monomial 0) s + (monomial 2) t + f) +
  (monomial 8) 1 = (3 * X + (monomial 8) 1 + (monomial 6) (t + 1)) + f + h + ((monomial 0) s +
  (monomial 1) u) + (monomial 5) 1) :
  (monomial 1) u + 5 * X + (g + (monomial 5) 1) + ((monomial 0) s + (monomial 2) t + f) +
  (monomial 8) 1 = (3 * X + (monomial 8) 1 + (monomial 6) (t + 1)) + f + h + ((monomial 0) s +
  (monomial 1) u) + (monomial 5) 1 :=
begin
--  convert hp using 1, ac_refl, -- works and takes 8s
--  sort_summands at ⊢ hp, assumption, --takes under 600ms
  sort_summands [g, (5 * X : R[X]), g, 3, f] at ⊢ hp,
  sort_summands [(5 * X : R[X]), monomial 2 t, monomial 0 s],
  sort_summands at ⊢ hp,
  assumption,
end

example (hp : f = g) :
  7 + f + (C r * X ^ 3 + 42) + X ^ 5 * h = C r * X ^ 3 + h * X ^ 5 + g + 7 + 42 :=
begin
  -- we move `f, g` to the right of their respective sides, so `congr` helps us remove the
  -- repeated term
  sort_summands [f, g],
  congr' 2, -- takes care of using assumption `hp`
  exact X_pow_mul,
end

example (hp : f = g) :
  7 + f + (monomial 3 r + 42) + X ^ 5 * h = monomial 3 r + h * X ^ 5 + g + 7 + 42 :=
begin
  sort_summands [f, g],
  congr' 3, -- takes care of using assumption `hp`
  exact X_pow_mul,
end

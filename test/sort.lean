import tactic.sort
import data.polynomial.basic

open polynomial tactic interactive
open_locale polynomial

variables {R : Type*} [semiring R] (f g h : R[X]) {r s t u : R} (r0 : t ≠ 0)

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
  7 + f + (monomial 3 r + 42) + X ^ 5 * h = monomial 3 r + h * X ^ 5 + g + 7 + 42 :=
begin
  sort_summands [f, g],
  congr' 3, -- takes care of using assumption `hp`
  exact X_pow_mul,
end

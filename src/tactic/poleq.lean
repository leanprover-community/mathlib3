/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.compute_degree

/-! # `poleq` a tactic for showing that two polynomials are equal -/

namespace polynomial

/- Adapted from Ruben's lemma. -/
lemma nat_degree_le_max {R : Type*} [semiring R] (n : ℕ) {p q : polynomial R}
  (pn : p.nat_degree ≤ n) (qn : q.nat_degree ≤ n) :
  (∀ i ≤ n, p.coeff i = q.coeff i) ↔ p = q :=
begin
  refine iff.trans _ ext_iff.symm,
  refine forall_congr (λ i, ⟨λ h, _, λ h _, h⟩),
  refine (le_or_lt i n).elim h (λ k, _),
  refine (coeff_eq_zero_of_nat_degree_lt (pn.trans_lt k)).trans
    (coeff_eq_zero_of_nat_degree_lt (qn.trans_lt k)).symm
end

end polynomial

namespace tactic
open compute_degree

/--  Given two expressions, `pol` representing a polynomial and `deg` representing an integer at
least equal to the degree of `pol`, `pol_deg_le pol deg` returns a proof of the inequality
`pol.nat_degree ≤ deg`.

Uses `compute_degree_le`, so `deg` should probably be at least as big as the largest "visible"
exponent.  -/
meta def pol_deg_le (pol deg : expr) : tactic expr := do
deg_pol ← mk_app `polynomial.nat_degree [pol],
tle ← to_expr ``((≤) : ℕ → ℕ → Prop) tt ff,
let deg_le  := tle.mk_app [deg_pol, deg],
(_, prf) ← solve_aux deg_le `[ compute_degree_le ],
return prf

/--  A tactic to convert an equality of polynomials into an equality of coefficients. -/
meta def interactive.show_deg_le : tactic unit := do
`(%%lhs = %%rhs) ← target,
[guess_left, guess_right] ← [lhs, rhs].mmap $ guess_degree,
tmax ← to_expr ``(max : ℕ → ℕ → ℕ) tt ff,
let max_deg := tmax.mk_app [guess_left, guess_right],
[prf_left, prf_right] ← [lhs, rhs].mmap $ λ e, pol_deg_le e max_deg,
refine ``((polynomial.nat_degree_le_max %%max_deg %%prf_left %%prf_right).mp _),
[i, H] ← intron' 2,
try `[norm_num at H]

end tactic

open polynomial

example {K : Type*} [field K] {p q a b c : K} :
  X ^ 3 + C p * X - C q = (X - C a) * (X - C b) * (X - C c) :=
begin
  show_deg_le,
  admit,
end

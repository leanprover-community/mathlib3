/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-
# Polynomials
Eventually, much of data/polynomial.lean should land here.
## Main results
- `card_pred_coeff_prod_X_sub_C` : yields that the trace is a coefficient of the characteristic polynomial
-/

noncomputable theory
open_locale big_operators

universes u w

variables {R : Type u} {α : Type w}

namespace polynomial

variables [comm_ring R]

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff (p : polynomial R) : R := ite (p.nat_degree = 0) 0 p.coeff (p.nat_degree - 1)

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
next_coeff (C c) = 0 := by {rw next_coeff, simp}

lemma next_coeff_of_pos_nat_degree (p : polynomial R) :
  0 < p.nat_degree → next_coeff p = p.coeff (p.nat_degree - 1) :=
by { intro h, rw next_coeff, rw if_neg, intro contra, rw contra at h, apply lt_irrefl 0 h, }

@[simp]
lemma next_coeff_X_sub_C_eq [nontrivial R] (c : R) : next_coeff (X - C c) = - c :=
by { rw next_coeff_of_pos_nat_degree; simp [nat_degree_X_sub_C] }

lemma pow_comp (p q : polynomial R) (k : ℕ) : (p ^ k).comp q = (p.comp q) ^ k :=
begin
  unfold comp, rw ← coe_eval₂_ring_hom, apply ring_hom.map_pow,
end


end polynomial

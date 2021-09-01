/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.multiset.sort
import data.pnat.basic
import data.rat.order

import tactic.norm_num
import tactic.field_simp
import tactic.interval_cases


/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

In this file we classify solutions to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`, for positive natural numbers `p`, `q`, and `r`.

The solutions are exactly of the form.
* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`

This inequality shows up in Lie theory,
in the classification of Dynkin diagrams, root systems, and semisimple Lie algebras.

## Main declarations

* `pqr.A' q r`, the multiset `{1,q,r}`
* `pqr.D' r`, the multiset `{2,2,r}`
* `pqr.E6`, the multiset `{2,3,3}`
* `pqr.E7`, the multiset `{2,3,4}`
* `pqr.E8`, the multiset `{2,3,5}`
* `pqr.classification`, the classification of solutions to `p⁻¹ + q⁻¹ + r⁻¹ > 1`

-/

namespace ADE_inequality

open multiset

/-- `A' q r := {1,q,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`. -/
def A' (q r : ℕ+) : multiset ℕ+ := {1,q,r}

/-- `A r := {1,1,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$. -/
def A  (r   : ℕ+) : multiset ℕ+ := A' 1 r

/-- `D' r := {2,2,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$. -/
def D' (r   : ℕ+) : multiset ℕ+ := {2,2,r}

/-- `E' r := {2,3,r}` is a `multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$. -/
def E' (r   : ℕ+) : multiset ℕ+ := {2,3,r}

/-- `E6 := {2,3,3}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$. -/
def E6            : multiset ℕ+ := E' 3

/-- `E7 := {2,3,4}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$. -/
def E7            : multiset ℕ+ := E' 4

/-- `E8 := {2,3,5}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$. -/
def E8            : multiset ℕ+ := E' 5

/-- `sum_inv pqr` for a `pqr : multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`. -/
def sum_inv (pqr : multiset ℕ+) : ℚ :=
multiset.sum $ pqr.map $ λ x, x⁻¹

lemma sum_inv_pqr (p q r : ℕ+) : sum_inv {p,q,r} = p⁻¹ + q⁻¹ + r⁻¹ :=
by simp only [sum_inv, coe_coe, add_zero, insert_eq_cons, add_assoc,
    map_cons, sum_cons, map_singleton, sum_singleton]

/-- A multiset `pqr` of positive natural numbers is `admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`. -/
def admissible (pqr : multiset ℕ+) : Prop :=
  (∃ q r, A' q r = pqr) ∨ (∃ r, D' r = pqr) ∨ (E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr)

lemma admissible_A' (q r : ℕ+) : admissible (A' q r) := or.inl ⟨q, r, rfl⟩
lemma admissible_D' (n : ℕ+) : admissible (D' n) := or.inr $ or.inl ⟨n, rfl⟩

lemma admissible_E'3 : admissible (E' 3) := or.inr $ or.inr $ or.inl rfl
lemma admissible_E'4 : admissible (E' 4) := or.inr $ or.inr $ or.inr $ or.inl rfl
lemma admissible_E'5 : admissible (E' 5) := or.inr $ or.inr $ or.inr $ or.inr rfl

lemma admissible_E6 : admissible (E6) := admissible_E'3
lemma admissible_E7 : admissible (E7) := admissible_E'4
lemma admissible_E8 : admissible (E8) := admissible_E'5

lemma admissible.one_lt_sum_inv {pqr : multiset ℕ+} :
  admissible pqr → 1 < sum_inv pqr :=
begin
  rw [admissible],
  rintro (⟨p', q', H⟩|⟨n, H⟩|H|H|H),
  { rw [← H, A', sum_inv_pqr, add_assoc],
    simp only [lt_add_iff_pos_right, pnat.one_coe, inv_one, nat.cast_one, coe_coe],
    apply add_pos; simp only [pnat.pos, nat.cast_pos, inv_pos] },
  { rw [← H, D', sum_inv_pqr],
    simp only [lt_add_iff_pos_right, pnat.one_coe, inv_one, nat.cast_one,
      coe_coe, pnat.coe_bit0, nat.cast_bit0],
    norm_num },
  all_goals { rw [← H, E', sum_inv_pqr], norm_num }
end

lemma lt_three {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r) (H : 1 < sum_inv {p, q, r}) :
  p < 3 :=
begin
  have h3 : (0:ℚ) < 3, by norm_num,
  contrapose! H, rw sum_inv_pqr,
  have h3q := H.trans hpq,
  have h3r := h3q.trans hqr,
  calc (p⁻¹ + q⁻¹ + r⁻¹ : ℚ) ≤ 3⁻¹ + 3⁻¹ + 3⁻¹ : add_le_add (add_le_add _ _) _
  ... = 1 : by norm_num,
  all_goals { rw inv_le_inv _ h3; [assumption_mod_cast, norm_num] }
end

lemma lt_four {q r : ℕ+} (hqr : q ≤ r) (H : 1 < sum_inv {2, q, r}) :
  q < 4 :=
begin
  have h4 : (0:ℚ) < 4, by norm_num,
  contrapose! H, rw sum_inv_pqr,
  have h4r := H.trans hqr,
  simp only [pnat.coe_bit0, nat.cast_bit0, pnat.one_coe, nat.cast_one, coe_coe],
  calc (2⁻¹ + q⁻¹ + r⁻¹ : ℚ) ≤ 2⁻¹ + 4⁻¹ + 4⁻¹ : add_le_add (add_le_add le_rfl _) _
  ... = 1 : by norm_num,
  all_goals { rw inv_le_inv _ h4; [assumption_mod_cast, norm_num] }
end

lemma lt_six {r : ℕ+} (H : 1 < sum_inv {2, 3, r}) :
  r < 6 :=
begin
  have h6 : (0:ℚ) < 6, by norm_num,
  contrapose! H, rw sum_inv_pqr,
  simp only [pnat.coe_bit0, nat.cast_bit0, pnat.one_coe, nat.cast_bit1, nat.cast_one,
    pnat.coe_bit1, coe_coe],
  calc (2⁻¹ + 3⁻¹ + r⁻¹ : ℚ) ≤ 2⁻¹ + 3⁻¹ + 6⁻¹ : add_le_add (add_le_add le_rfl le_rfl) _
  ... = 1 : by norm_num,
  rw inv_le_inv _ h6; [assumption_mod_cast, norm_num]
end

lemma admissible_of_one_lt_sum_inv_aux' {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r)
  (H : 1 < sum_inv {p,q,r}) :
  admissible {p,q,r} :=
begin
  have hp3 : p < 3 := lt_three hpq hqr H,
  interval_cases p,
  { exact admissible_A' q r },
  have hq4 : q < 4 := lt_four hqr H,
  interval_cases q,
  { exact admissible_D' r },
  have hr6 : r < 6 := lt_six H,
  interval_cases r,
  { exact admissible_E6 },
  { exact admissible_E7 },
  { exact admissible_E8 }
end

lemma admissible_of_one_lt_sum_inv_aux :
  ∀ {pqr : list ℕ+} (hs : pqr.sorted (≤)) (hl : pqr.length = 3) (H : 1 < sum_inv pqr),
    admissible pqr
| [p,q,r] hs hl H :=
begin
  obtain ⟨⟨hpq, -⟩, hqr⟩ : (p ≤ q ∧ p ≤ r) ∧ q ≤ r,
  simpa using hs,
  exact admissible_of_one_lt_sum_inv_aux' hpq hqr H,
end

lemma admissible_of_one_lt_sum_inv {p q r : ℕ+} (H : 1 < sum_inv {p,q,r}) :
  admissible {p,q,r} :=
begin
  simp only [admissible],
  let S := sort ((≤) : ℕ+ → ℕ+ → Prop) {p,q,r},
  have hS : S.sorted (≤) := sort_sorted _ _,
  have hpqr : ({p,q,r} : multiset ℕ+) = S := (sort_eq has_le.le {p, q, r}).symm,
  simp only [hpqr] at *,
  apply admissible_of_one_lt_sum_inv_aux hS _ H,
  simp only [S, length_sort],
  dec_trivial,
end

/-- A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
lemma classification (p q r : ℕ+) :
  1 < sum_inv {p,q,r} ↔ admissible {p,q,r} :=
⟨admissible_of_one_lt_sum_inv, admissible.one_lt_sum_inv⟩

end ADE_inequality

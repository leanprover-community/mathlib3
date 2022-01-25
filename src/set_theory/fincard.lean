/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import set_theory.cardinal

/-!
# Finite Cardinality Functions

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `enat.card α = ⊤`.

-/

open cardinal
noncomputable theory

variable {α : Type*}

namespace nat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
def card (α : Type*) : ℕ := (mk α).to_nat

@[simp]
lemma card_eq_fintype_card [fintype α] : card α = fintype.card α := mk_to_nat_eq_card

@[simp]
lemma card_eq_zero_of_infinite [infinite α] : card α = 0 := mk_to_nat_of_infinite

end nat

namespace enat

/-- `enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `enat.card α = ⊤`. -/
def card (α : Type*) : enat := (mk α).to_enat

@[simp]
lemma card_eq_coe_fintype_card [fintype α] : card α = fintype.card α := mk_to_enat_eq_coe_card

@[simp]
lemma card_eq_top_of_infinite [infinite α] : card α = ⊤ := mk_to_enat_of_infinite

end enat

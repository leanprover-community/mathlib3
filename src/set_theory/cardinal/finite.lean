/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.zmod.defs
import set_theory.cardinal.nat_enat

/-!
# Finite Cardinality Functions

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `part_enat.card α` is the cardinality of `α` as an extended natural number
  (`part ℕ` implementation). If `α` is infinite, `part_enat.card α = ⊤`.
-/

open cardinal
noncomputable theory
open_locale big_operators cardinal

variables {α β : Sort*} {γ δ : Type*}

namespace enat

lemma card_eq_two_iff : #ₑ γ = 2 ↔ ∃ x y : γ, x ≠ y ∧ {x, y} = @set.univ γ :=
by rw [← to_enat_mk, ← nat.cast_two, to_enat_eq_nat, nat.cast_two, mk_eq_two_iff]

lemma card_eq_two_iff' (x : γ) : #ₑ γ = 2 ↔ ∃! y, y ≠ x :=
by rw [card_eq_two_iff, ← mk_eq_two_iff, mk_eq_two_iff']

@[simp] lemma card_pi {β : γ → Sort*} [fintype γ] : #ₑ (Π a, β a) = ∏ a, #ₑ (β a) :=
calc #ₑ (Π a, β a) = #ₑ (Π a, plift (β a)) :
  card_congr $ equiv.Pi_congr_right $ λ a, equiv.plift.symm
... = ∏ a, #ₑ (β a) :
  by simp_rw [← to_enat_mk, mk_pi, prod_eq_of_fintype, to_enat_lift, map_prod, to_enat_mk,
    card_plift]

@[simp] lemma card_fun [finite α] : #ₑ (α → β) = (#ₑ β) ^ #ₙ α :=
begin
  haveI := fintype.of_finite (plift α),
  rw [card_congr (equiv.plift.symm.Pi_congr_left' _), card_pi, finset.prod_const, finset.card_univ,
    ← nat.card_fintype, nat.card_plift]
end

end enat

namespace nat

lemma card_eq_two_iff : #ₙ γ = 2 ↔ ∃ x y : γ, x ≠ y ∧ {x, y} = @set.univ γ :=
(enat.to_nat_eq_iff two_ne_zero).trans enat.card_eq_two_iff

lemma card_eq_two_iff' (x : γ) : #ₙ γ = 2 ↔ ∃! y, y ≠ x :=
(enat.to_nat_eq_iff two_ne_zero).trans (enat.card_eq_two_iff' x)

lemma card_pi {β : γ → Sort*} [fintype γ] : #ₙ (Π a, β a) = ∏ a, #ₙ (β a) :=
by simp only [nat.card, enat.card_pi, map_prod]

lemma card_fun [finite α] : #ₙ (α → β) = (#ₙ β) ^ #ₙ α :=
by simp only [nat.card, enat.card_fun, map_pow]

@[simp] lemma card_zmod (n : ℕ) : #ₙ (zmod n) = n :=
by { cases n, exacts [card_infinite _, card_fin _] }

end nat

/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import set_theory.cardinal.basic

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

variables {α β : Type*}

namespace nat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type*) : ℕ := (mk α).to_nat

@[simp]
lemma card_eq_fintype_card [fintype α] : nat.card α = fintype.card α := mk_to_nat_eq_card

@[simp]
lemma card_eq_zero_of_infinite [infinite α] : nat.card α = 0 := mk_to_nat_of_infinite

lemma card_eq_of_equiv (f : α ≃ β) : nat.card α = nat.card β :=
begin
  have : ulift α ≃ ulift β := (equiv.ulift.trans f).trans equiv.ulift.symm,
  have := cardinal.to_nat_congr this,
  simpa using this,
end

lemma card_eq_of_bijective (f : α → β) (hf : function.bijective f) : nat.card α = nat.card β :=
card_eq_of_equiv (equiv.of_bijective f hf)

lemma card_eq_of_equiv_fin {α : Type*} {n : ℕ}
  (f : α ≃ fin n) : nat.card α = n :=
by simpa using card_eq_of_equiv f

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equiv_fin_of_card_pos {α : Type*} (h : 0 < nat.card α) :
  α ≃ fin (nat.card α) :=
begin
  casesI fintype_or_infinite α,
  { simpa using fintype.equiv_fin α },
  { simpa using h },
end

lemma card_of_subsingleton (a : α) [subsingleton α] : nat.card α = 1 :=
begin
  rw [card_eq_fintype_card],
  convert fintype.card_of_subsingleton a,
end

@[simp] lemma card_unique [unique α] : nat.card α = 1 :=
card_of_subsingleton default

lemma card_eq_one_iff_nonempty_unique : nat.card α = 1 ↔ nonempty (unique α) :=
⟨λ h, begin
  have := @equiv_fin_of_card_pos α (by simp [h]),
  haveI := fintype.of_equiv _ this.symm,
  rw ← fintype.card_eq_one_iff_nonempty_unique,
  simpa using h,
end, λ ⟨_⟩, by exactI card_unique⟩

theorem card_of_is_empty [is_empty α] : nat.card α = 0 := by simp

@[simp] lemma card_prod (α β : Type*) : nat.card (α × β) = nat.card α * nat.card β :=
begin
  casesI fintype_or_infinite α,
  { casesI fintype_or_infinite β,
    { simp },
    { casesI is_empty_or_nonempty α; simp } },
  { casesI is_empty_or_nonempty β; simp }
end

@[simp] lemma card_ulift (α : Type*) : nat.card (ulift α) = nat.card α :=
card_eq_of_equiv equiv.ulift

@[simp] lemma card_plift (α : Type*) : nat.card (plift α) = nat.card α :=
card_eq_of_equiv equiv.plift

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

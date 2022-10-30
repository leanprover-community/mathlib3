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
universes u v

variables {α : Type u} {β : Type v}

protected def enat.card (α : Type*) : ℕ∞ := (#α).to_enat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def nat.card (α : Type*) : ℕ := (#α).to_nat

@[simp] lemma nat.card_fintype [fintype α] : nat.card α = fintype.card α :=
by rw [nat.card, mk_fintype, to_nat_nat]

namespace enat

lemma card_congr (e : α ≃ β) : enat.card α = enat.card β :=
by rw [enat.card, ← to_enat_lift, lift_mk_eq.2 ⟨e⟩, to_enat_lift, enat.card]

@[simp] lemma card_sum : enat.card (α ⊕ β) = enat.card α + enat.card β :=
by simp only [enat.card, mk_sum, map_add, to_enat_lift]

@[simp] lemma card_prod : enat.card (α × β) = enat.card α * enat.card β :=
by simp only [enat.card, mk_prod, map_mul, to_enat_lift]

@[simp] lemma card_option : enat.card (option α) = enat.card α + 1 :=
by simp only [enat.card, mk_option, map_add, map_one]

lemma card_eq_top : enat.card α = ⊤ ↔ infinite α :=
to_enat_eq_top.trans infinite_iff.symm

@[simp] lemma card_infinite [infinite α] : enat.card α = ⊤ := card_eq_top.2 ‹_›

lemma card_fintype [fintype α] : enat.card α = fintype.card α :=
by rw [enat.card, mk_fintype, to_enat_nat]

@[simp] lemma card_finite [finite α] : enat.card α = nat.card α :=
by { casesI nonempty_fintype α, rw [card_fintype, nat.card_fintype] }

@[simp] lemma to_nat_card : (enat.card α).to_nat = nat.card α := rfl

end enat

namespace nat

@[simp] lemma card_eq_zero_of_infinite [infinite α] : nat.card α = 0 :=
by rw [nat.card, to_nat_apply_of_aleph_0_le (aleph_0_le_mk α)]

lemma finite_of_card_ne_zero (h : nat.card α ≠ 0) : finite α :=
not_infinite_iff_finite.mp $ h ∘ @nat.card_eq_zero_of_infinite α

lemma card_congr (f : α ≃ β) : nat.card α = nat.card β :=
by simp only [← enat.to_nat_card, enat.card_congr f]

lemma card_eq_of_bijective (f : α → β) (hf : function.bijective f) : nat.card α = nat.card β :=
card_congr (equiv.of_bijective f hf)

lemma card_eq_of_equiv_fin {n : ℕ} (f : α ≃ fin n) : nat.card α = n :=
by simpa using card_congr f

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equiv_fin_of_card_pos {α : Type*} (h : nat.card α ≠ 0) :
  α ≃ fin (nat.card α) :=
begin
  haveI : finite α := finite_of_card_ne_zero h,
  haveI := fintype.of_finite α,
  simpa using fintype.equiv_fin α
end

lemma card_of_subsingleton (a : α) [subsingleton α] : nat.card α = 1 :=
begin
  letI := fintype.of_subsingleton a,
  rw [card_eq_fintype_card, fintype.card_of_subsingleton a]
end

@[simp] lemma card_unique [unique α] : nat.card α = 1 :=
card_of_subsingleton default

lemma card_eq_one_iff_unique : nat.card α = 1 ↔ subsingleton α ∧ nonempty α :=
cardinal.to_nat_eq_one_iff_unique

lemma card_eq_two_iff : nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @set.univ α :=
(to_nat_eq_iff two_ne_zero).trans $ iff.trans (by rw [nat.cast_two]) mk_eq_two_iff

lemma card_eq_two_iff' (x : α) : nat.card α = 2 ↔ ∃! y, y ≠ x :=
(to_nat_eq_iff two_ne_zero).trans $ iff.trans (by rw [nat.cast_two]) (mk_eq_two_iff' x)

theorem card_of_is_empty [is_empty α] : nat.card α = 0 := by simp

@[simp] lemma card_prod (α β : Type*) : nat.card (α × β) = nat.card α * nat.card β :=
by simp only [nat.card, mk_prod, to_nat_mul, to_nat_lift]

@[simp] lemma card_ulift (α : Type*) : nat.card (ulift α) = nat.card α :=
card_congr equiv.ulift

@[simp] lemma card_plift (α : Type*) : nat.card (plift α) = nat.card α :=
card_congr equiv.plift

lemma card_pi {β : α → Type*} [fintype α] : nat.card (Π a, β a) = ∏ a, nat.card (β a) :=
by simp_rw [nat.card, mk_pi, prod_eq_of_fintype, to_nat_lift, to_nat_finset_prod]

lemma card_fun [finite α] : nat.card (α → β) = nat.card β ^ nat.card α :=
begin
  haveI := fintype.of_finite α,
  rw [nat.card_pi, finset.prod_const, finset.card_univ, ←nat.card_eq_fintype_card],
end

@[simp] lemma card_zmod (n : ℕ) : nat.card (zmod n) = n :=
begin
  cases n,
  { exact nat.card_eq_zero_of_infinite },
  { rw [nat.card_eq_fintype_card, zmod.card] },
end

end nat

namespace part_enat

/-- `part_enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `part_enat.card α = ⊤`. -/
def card (α : Type*) : part_enat := (mk α).to_part_enat

@[simp]
lemma card_eq_coe_fintype_card [fintype α] : card α = fintype.card α := mk_to_part_enat_eq_coe_card

@[simp]
lemma card_eq_top_of_infinite [infinite α] : card α = ⊤ := mk_to_part_enat_of_infinite

end part_enat

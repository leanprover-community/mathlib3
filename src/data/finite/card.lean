/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import data.finite.basic

/-!

# Cardinality of finite types

The cardinality of a finite type `α` is given by `nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `finite` instance
for the type. (Note: we could have defined a `finite.card` that required you to
supply a `finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `set_theory.cardinal.finite` module.

-/

noncomputable theory
open_locale classical

variables {α β γ : Type*}

/-! ### Cardinality as a nat with top -/

namespace nat

/-- The cardinality of a type as a `with_top ℕ`.-/
def card_top (α : Type*) : with_top ℕ :=
if h : finite α then @fintype.card α (@fintype.of_finite α h) else ⊤

@[simp] theorem card_top_eq_fintype_card (α : Type*) [fintype α] : card_top α = fintype.card α :=
begin
  rw [card_top, dif_pos (finite.of_fintype' α), with_top.coe_eq_coe],
  apply fintype.card_congr' rfl
end

@[simp] theorem card_top_eq_top (α : Type*) [h : infinite α] : card_top α = ⊤ :=
dif_neg $ not_finite_iff_infinite.2 h

theorem card_top_congr (e : α ≃ β) : card_top α = card_top β :=
begin
  casesI fintype_or_infinite α,
  { haveI := fintype.of_equiv α e,
    rw [card_top_eq_fintype_card, card_top_eq_fintype_card, with_top.coe_eq_coe],
    exact fintype.card_congr e },
  { haveI := infinite.of_injective e e.injective,
    simp }
end

alias card_top_congr ← _root_.equiv.card_top_eq

theorem card_top_eq_zero (α : Type*) [is_empty α] : card_top α = 0 := by simp
theorem card_top_eq_one (α : Type*) [unique α] : card_top α = 1 := by simp
theorem card_top_empty : card_top empty = 0 := by simp
theorem card_top_pempty : card_top pempty = 0 := by simp
theorem card_top_unit : card_top unit = 1 := by simp
theorem card_top_punit : card_top punit = 1 := by simp
@[simp] theorem card_top_bool : card_top bool = 2 := card_top_eq_fintype_card bool
theorem card_top_fin (n : ℕ) : card_top (fin n) = n := by simp
theorem card_top_nat : card_top ℕ = ⊤ := by simp
theorem card_top_int : card_top ℤ = ⊤ := by simp

theorem card_top_eq_of_equiv_fin {n} (e : α ≃ fin n) : card_top α = n :=
by simpa using e.card_top_eq

@[simp] theorem card_top_eq_zero_iff : card_top α = 0 ↔ is_empty α :=
by casesI fintype_or_infinite α; simp

@[simp] theorem card_top_eq_one_iff : card_top α = 1 ↔ nonempty (unique α) :=
by { casesI fintype_or_infinite α; simp, apply_instance }

@[simp] theorem card_top_sum (α β : Type*) : card_top (α ⊕ β) = card_top α + card_top β :=
by { casesI fintype_or_infinite α; casesI fintype_or_infinite β; simp [with_top.coe_add] }

@[simp] theorem card_top_prod (α β : Type*) : card_top (α × β) = card_top α * card_top β :=
begin
  casesI fintype_or_infinite α;
  casesI fintype_or_infinite β,
  { simp [with_top.coe_mul] },
  { casesI is_empty_or_nonempty α,
    { simp [with_top.coe_zero] },
    { simp } },
  { casesI is_empty_or_nonempty β,
    { simp [with_top.coe_zero] },
    { simp } },
  { simp }
end

/-! ### Cardinality as a nat -/

/-- The cardinality of a type as a natural numbers. Infinite types are mapped to `0`. -/
def card (α : Type*) : ℕ := (card_top α).untop' 0

@[simp] theorem card_eq_fintype_card (α : Type*) [fintype α] : card α = fintype.card α :=
by { rw card, simp }

@[simp] theorem card_top_eq_card (α : Type*) [finite α] : card_top α = card α :=
by { rw card, haveI := fintype.of_finite α, simp }

@[simp] theorem card_eq_zero_of_infinite (α : Type*) [h : infinite α] : card α = 0 :=
by { rw card, simp }

theorem card_congr (e : α ≃ β) : card α = card β := by rw [card, card, e.card_top_eq]

alias card_congr ← _root_.equiv.card_eq

theorem card_eq_zero_of_empty (α : Type*) [is_empty α] : card α = 0 := by simp
theorem card_eq_one (α : Type*) [unique α] : card α = 1 := by simp
theorem card_empty : card empty = 0 := by simp
theorem card_pempty : card pempty = 0 := by simp
theorem card_unit : card unit = 1 := by simp
theorem card_punit : card punit = 1 := by simp
theorem card_bool : card bool = 2 := by simp
theorem card_fin (n : ℕ) : card (fin n) = n := by simp
theorem card_nat : card ℕ = 0 := by simp
theorem card_int : card ℤ = 0 := by simp

theorem card_eq_of_equiv_fin {n} (e : α ≃ fin n) : card α = n := by simpa using e.card_eq

end nat

/-- There is (noncomputably) an equivalence between a finite type `α` and `fin (nat.card α)`. -/
def finite.equiv_fin (α : Type*) [finite α] : α ≃ fin (nat.card α) :=
begin
  have := (finite.exists_equiv_fin α).some_spec.some,
  rwa nat.card_eq_of_equiv_fin this
end

/-- Similar to `finite.equiv_fin` but with control over the term used for the cardinality. -/
def finite.equiv_fin_of_card_eq [finite α] {n : ℕ} (h : nat.card α = n) : α ≃ fin n :=
by { subst h, apply finite.equiv_fin }

lemma nat.card_eq (α : Type*) :
  nat.card α = if h : finite α then by exactI @fintype.card α (fintype.of_finite α) else 0 :=
begin
  casesI finite_or_infinite α,
  { letI := fintype.of_finite α,
    simp only [*, nat.card_eq_fintype_card, dif_pos] },
  { simp [*, not_finite_iff_infinite.mpr h] },
end

lemma finite.card_pos_iff [finite α] : 0 < nat.card α ↔ nonempty α :=
begin
  haveI := fintype.of_finite α,
  simp only [nat.card_eq_fintype_card],
  exact fintype.card_pos_iff,
end

namespace finite

lemma card_eq [finite α] [finite β] : nat.card α = nat.card β ↔ nonempty (α ≃ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp [fintype.card_eq] }

lemma card_le_one_iff_subsingleton [finite α] : nat.card α ≤ 1 ↔ subsingleton α :=
by { haveI := fintype.of_finite α, simp [fintype.card_le_one_iff_subsingleton] }

lemma one_lt_card_iff_nontrivial [finite α] : 1 < nat.card α ↔ nontrivial α :=
by { haveI := fintype.of_finite α, simp [fintype.one_lt_card_iff_nontrivial] }

lemma one_lt_card [finite α] [h : nontrivial α] : 1 < nat.card α :=
one_lt_card_iff_nontrivial.mpr h

@[simp] lemma card_option [finite α] : nat.card (option α) = nat.card α + 1 :=
by { haveI := fintype.of_finite α, simp }

lemma card_le_of_injective [finite β] (f : α → β) (hf : function.injective f) :
  nat.card α ≤ nat.card β :=
by { haveI := fintype.of_finite β, haveI := fintype.of_injective f hf,
     simpa using fintype.card_le_of_injective f hf }

lemma card_le_of_embedding [finite β] (f : α ↪ β) : nat.card α ≤ nat.card β :=
card_le_of_injective _ f.injective

lemma card_le_of_surjective [finite α] (f : α → β) (hf : function.surjective f) :
  nat.card β ≤ nat.card α :=
by { haveI := fintype.of_finite α, haveI := fintype.of_surjective f hf,
     simpa using fintype.card_le_of_surjective f hf }

lemma card_eq_zero_iff [finite α] : nat.card α = 0 ↔ is_empty α :=
by { haveI := fintype.of_finite α, simp [fintype.card_eq_zero_iff] }

@[simp] theorem card_sum [finite α] [finite β] : nat.card (α ⊕ β) = nat.card α + nat.card β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp }

@[simp] theorem card_prod [finite α] [finite β] : nat.card (α × β) = nat.card α * nat.card β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp }

end finite

theorem finite.card_subtype_le [finite α] (p : α → Prop) :
  nat.card {x // p x} ≤ nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_le p }

theorem finite.card_subtype_lt [finite α] {p : α → Prop} {x : α} (hx : ¬ p x) :
  nat.card {x // p x} < nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_lt hx }

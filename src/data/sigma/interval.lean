/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sigma.order
import order.locally_finite

/-!
# Finite intervals in a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/

open finset function

namespace sigma
variables {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/

section disjoint
variables [decidable_eq ι] [Π i, preorder (α i)] [Π i, locally_finite_order (α i)]

instance : locally_finite_order (Σ i, α i) :=
{ finset_Icc := sigma_lift (λ _, Icc),
  finset_Ico := sigma_lift (λ _, Ico),
  finset_Ioc := sigma_lift (λ _, Ioc),
  finset_Ioo := sigma_lift (λ _, Ioo),
  finset_mem_Icc := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, le_def, mem_Icc, exists_and_distrib_left, ←exists_and_distrib_right,
      ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ico := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ico, exists_and_distrib_left,
      ←exists_and_distrib_right, ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ioc := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ioc, exists_and_distrib_left,
      ←exists_and_distrib_right, ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ioo := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sigma_lift, lt_def, mem_Ioo, exists_and_distrib_left, ←exists_and_distrib_right,
      ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end }

section
variables (a b : Σ i, α i)

lemma card_Icc : (Icc a b).card = if h : a.1 = b.1 then (Icc (h.rec a.2) b.2).card else 0 :=
card_sigma_lift _ _ _

lemma card_Ico : (Ico a b).card = if h : a.1 = b.1 then (Ico (h.rec a.2) b.2).card else 0 :=
card_sigma_lift _ _ _

lemma card_Ioc : (Ioc a b).card = if h : a.1 = b.1 then (Ioc (h.rec a.2) b.2).card else 0 :=
card_sigma_lift _ _ _

lemma card_Ioo : (Ioo a b).card = if h : a.1 = b.1 then (Ioo (h.rec a.2) b.2).card else 0 :=
card_sigma_lift _ _ _

end

variables (i : ι) (a b : α i)

@[simp] lemma Icc_mk_mk : Icc (⟨i, a⟩ : sigma α) ⟨i, b⟩ = (Icc a b).map (embedding.sigma_mk i) :=
dif_pos rfl

@[simp] lemma Ico_mk_mk : Ico (⟨i, a⟩ : sigma α) ⟨i, b⟩ = (Ico a b).map (embedding.sigma_mk i) :=
dif_pos rfl

@[simp] lemma Ioc_mk_mk : Ioc (⟨i, a⟩ : sigma α) ⟨i, b⟩ = (Ioc a b).map (embedding.sigma_mk i) :=
dif_pos rfl

@[simp] lemma Ioo_mk_mk : Ioo (⟨i, a⟩ : sigma α) ⟨i, b⟩ = (Ioo a b).map (embedding.sigma_mk i) :=
dif_pos rfl

end disjoint
end sigma

/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.finset.sort
import data.fintype.basic

/-!
# Sorting a finite type

This file provides two equivalences for linearly ordered fintypes:
* `mono_equiv_of_fin`: Order isomorphism between `α` and `fin (card α)`.
* `fin_sum_equiv_of_finset`: Equivalence between `α` and `fin m ⊕ fin n` where `m` and `n` are
  respectively the cardinalities of some `finset α` and its complement.
-/

open finset

/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`mono_equiv_of_fin α h` is the increasing bijection between `fin k` and `α`. Here, `h` is a proof
that the cardinality of `α` is `k`. We use this instead of an isomorphism `fin (card α) ≃o α` to
avoid casting issues in further uses of this function. -/
def mono_equiv_of_fin (α : Type*) [fintype α] [linear_order α] {k : ℕ} (h : fintype.card α = k) :
  fin k ≃o α :=
(univ.order_iso_of_fin h).trans $ (order_iso.set_congr _ _ coe_univ).trans order_iso.set.univ

variables {α : Type*} [decidable_eq α] [fintype α] [linear_order α] {m n : ℕ} {s : finset α}

/-- If `α` is a linearly ordered fintype, `s : finset α` has cardinality `m` and its complement has
cardinality `n`, then `fin m ⊕ fin n ≃ α`. The equivalence sends elements of `fin m` to
elements of `s` and elements of `fin n` to elements of `sᶜ` while preserving order on each
"half" of `fin m ⊕ fin n` (using `set.order_iso_of_fin`). -/
def fin_sum_equiv_of_finset (hm : s.card = m) (hn : sᶜ.card = n) : fin m ⊕ fin n ≃ α :=
calc fin m ⊕ fin n ≃ (s : set α) ⊕ (sᶜ : set α) :
  equiv.sum_congr (s.order_iso_of_fin hm).to_equiv $
    (sᶜ.order_iso_of_fin hn).to_equiv.trans $ equiv.set.of_eq s.coe_compl
... ≃ α : equiv.set.sum_compl _

@[simp] lemma fin_sum_equiv_of_finset_inl (hm : s.card = m) (hn : sᶜ.card = n) (i : fin m) :
  fin_sum_equiv_of_finset hm hn (sum.inl i) = s.order_emb_of_fin hm i :=
rfl

@[simp] lemma fin_sum_equiv_of_finset_inr (hm : s.card = m) (hn : sᶜ.card = n) (i : fin n) :
  fin_sum_equiv_of_finset hm hn (sum.inr i) = sᶜ.order_emb_of_fin hn i :=
rfl

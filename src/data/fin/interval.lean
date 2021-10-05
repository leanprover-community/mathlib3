/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.nat.interval

/-!
# Finite intervals in `fin n`

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

@Yaël: Add `finset.Ico`. Coming very soon.
-/

open finset fin

variables (n : ℕ)

instance : locally_finite_order (fin n) := subtype.locally_finite_order _

namespace fin
variables {n} (a b : fin n)

lemma Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).subtype (λ x, x < n) := rfl
lemma Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).subtype (λ x, x < n) := rfl
lemma Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).subtype (λ x, x < n) := rfl

@[simp] lemma map_subtype_embedding_Icc :
  (Icc a b).map (function.embedding.subtype _) = Icc (a : ℕ) b :=
map_subtype_embedding_Icc _ _ _ (λ _ c x _ hx _, hx.trans_lt)

@[simp] lemma map_subtype_embedding_Ioc :
  (Ioc a b).map (function.embedding.subtype _) = Ioc (a : ℕ) b :=
map_subtype_embedding_Ioc _ _ _ (λ _ c x _ hx _, hx.trans_lt)

@[simp] lemma map_subtype_embedding_Ioo :
  (Ioo a b).map (function.embedding.subtype _) = Ioo (a : ℕ) b :=
map_subtype_embedding_Ioo _ _ _ (λ _ c x _ hx _, hx.trans_lt)

@[simp] lemma card_Icc : (Icc a b).card = b + 1 - a :=
by rw [←nat.card_Icc, ←map_subtype_embedding_Icc, card_map]

@[simp] lemma card_Ioc : (Ioc a b).card = b - a :=
by rw [←nat.card_Ioc, ←map_subtype_embedding_Ioc, card_map]

@[simp] lemma card_Ioo : (Ioo a b).card = b - a - 1 :=
by rw [←nat.card_Ioo, ←map_subtype_embedding_Ioo, card_map]

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [←card_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [←card_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [←card_Ioo, fintype.card_of_finset]

end fin

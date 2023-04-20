/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.nat.interval
import data.finset.locally_finite

/-!
# Finite intervals in `fin n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open finset fin function

open_locale big_operators

variables (n : ℕ)

instance : locally_finite_order (fin n) :=
order_iso.locally_finite_order fin.order_iso_subtype

instance : locally_finite_order_bot (fin n) :=
order_iso.locally_finite_order_bot fin.order_iso_subtype

instance : Π n, locally_finite_order_top (fin n)
| 0 := is_empty.to_locally_finite_order_top
| (n + 1) := infer_instance

namespace fin
variables {n} (a b : fin n)

lemma Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).fin n := rfl
lemma Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).fin n := rfl
lemma Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).fin n := rfl
lemma Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).fin n := rfl

@[simp] lemma map_subtype_embedding_Icc : (Icc a b).map fin.coe_embedding = Icc a b :=
by simp [Icc_eq_finset_subtype, finset.fin, finset.map_map, Icc_filter_lt_of_lt_right]

@[simp] lemma map_subtype_embedding_Ico : (Ico a b).map fin.coe_embedding = Ico a b :=
by simp [Ico_eq_finset_subtype, finset.fin, finset.map_map]

@[simp] lemma map_subtype_embedding_Ioc : (Ioc a b).map fin.coe_embedding = Ioc a b :=
by simp [Ioc_eq_finset_subtype, finset.fin, finset.map_map, Ioc_filter_lt_of_lt_right]

@[simp] lemma map_subtype_embedding_Ioo : (Ioo a b).map fin.coe_embedding = Ioo a b :=
by simp [Ioo_eq_finset_subtype, finset.fin, finset.map_map]

@[simp] lemma card_Icc : (Icc a b).card = b + 1 - a :=
by rw [←nat.card_Icc, ←map_subtype_embedding_Icc, card_map]

@[simp] lemma card_Ico : (Ico a b).card = b - a :=
by rw [←nat.card_Ico, ←map_subtype_embedding_Ico, card_map]

@[simp] lemma card_Ioc : (Ioc a b).card = b - a :=
by rw [←nat.card_Ioc, ←map_subtype_embedding_Ioc, card_map]

@[simp] lemma card_Ioo : (Ioo a b).card = b - a - 1 :=
by rw [←nat.card_Ioo, ←map_subtype_embedding_Ioo, card_map]

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [←card_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = b - a :=
by rw [←card_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [←card_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [←card_Ioo, fintype.card_of_finset]

lemma Ici_eq_finset_subtype : Ici a = (Icc (a : ℕ) n).fin n := by { ext, simp }
lemma Ioi_eq_finset_subtype : Ioi a = (Ioc (a : ℕ) n).fin n := by { ext, simp }
lemma Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).fin n := rfl
lemma Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).fin n := rfl

@[simp] lemma map_subtype_embedding_Ici : (Ici a).map fin.coe_embedding = Icc a (n - 1) :=
begin
  ext x,
  simp only [exists_prop, embedding.coe_subtype, mem_Ici, mem_map, mem_Icc],
  split,
  { rintro ⟨x, hx, rfl⟩,
    exact ⟨hx, le_tsub_of_add_le_right $ x.2⟩ },
  cases n,
  { exact fin.elim0 a },
  { exact λ hx, ⟨⟨x, nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩ }
end

@[simp] lemma map_subtype_embedding_Ioi : (Ioi a).map fin.coe_embedding = Ioc a (n - 1) :=
begin
  ext x,
  simp only [exists_prop, embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc],
  split,
  { rintro ⟨x, hx, rfl⟩,
    exact ⟨hx, le_tsub_of_add_le_right $ x.2⟩ },
  cases n,
  { exact fin.elim0 a },
  { exact λ hx, ⟨⟨x, nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩ }
end

@[simp] lemma map_subtype_embedding_Iic : (Iic b).map fin.coe_embedding = Iic b :=
by simp [Iic_eq_finset_subtype, finset.fin, finset.map_map, Iic_filter_lt_of_lt_right]

@[simp] lemma map_subtype_embedding_Iio : (Iio b).map fin.coe_embedding = Iio b :=
by simp [Iio_eq_finset_subtype, finset.fin, finset.map_map]

@[simp] lemma card_Ici : (Ici a).card = n - a :=
by { cases n, { exact fin.elim0 a }, rw [←card_map, map_subtype_embedding_Ici, nat.card_Icc], refl }

@[simp] lemma card_Ioi : (Ioi a).card = n - 1 - a :=
by { rw [←card_map, map_subtype_embedding_Ioi, nat.card_Ioc] }

@[simp] lemma card_Iic : (Iic b).card = b + 1 :=
by rw [←nat.card_Iic b, ←map_subtype_embedding_Iic, card_map]

@[simp] lemma card_Iio : (Iio b).card = b :=
by rw [←nat.card_Iio b, ←map_subtype_embedding_Iio, card_map]

@[simp] lemma card_fintype_Ici : fintype.card (set.Ici a) = n - a :=
by rw [fintype.card_of_finset, card_Ici]

@[simp] lemma card_fintype_Ioi : fintype.card (set.Ioi a) = n - 1 - a :=
by rw [fintype.card_of_finset, card_Ioi]

@[simp] lemma card_fintype_Iic : fintype.card (set.Iic b) = b + 1 :=
by rw [fintype.card_of_finset, card_Iic]

@[simp] lemma card_fintype_Iio : fintype.card (set.Iio b) = b :=
by rw [fintype.card_of_finset, card_Iio]

end fin

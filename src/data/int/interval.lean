/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.int.basic
import data.nat.interval

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open finset int

instance : locally_finite_order ℤ :=
{ finset_Icc := λ a b, (finset.range (b + 1 - a).to_nat).map $
    nat.cast_embedding.trans $ add_left_embedding a,
  finset_Ico := λ a b, (finset.range (b - a).to_nat).map $
    nat.cast_embedding.trans $ add_left_embedding a,
  finset_Ioc := λ a b, (finset.range (b - a).to_nat).map $
    nat.cast_embedding.trans $ add_left_embedding (a + 1),
  finset_Ioo := λ a b, (finset.range (b - a - 1).to_nat).map $
    nat.cast_embedding.trans $ add_left_embedding (a + 1),
  finset_mem_Icc := λ a b x, begin
    simp_rw [mem_map, exists_prop, mem_range, int.lt_to_nat, function.embedding.trans_apply,
      nat.cast_embedding_apply, add_left_embedding_apply, nat_cast_eq_coe_nat],
    split,
    { rintro ⟨a, h, rfl⟩,
      rw [lt_sub_iff_add_lt, int.lt_add_one_iff, add_comm] at h,
      exact ⟨int.le.intro rfl, h⟩ },
    { rintro ⟨ha, hb⟩,
      use (x - a).to_nat,
      rw ←lt_add_one_iff at hb,
      rw to_nat_sub_of_le ha,
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end,
  finset_mem_Ico := λ a b x, begin
    simp_rw [mem_map, exists_prop, mem_range, int.lt_to_nat, function.embedding.trans_apply,
      nat.cast_embedding_apply, add_left_embedding_apply, nat_cast_eq_coe_nat],
    split,
    { rintro ⟨a, h, rfl⟩,
      exact ⟨int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩ },
    { rintro ⟨ha, hb⟩,
      use (x - a).to_nat,
      rw to_nat_sub_of_le ha,
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end,
  finset_mem_Ioc := λ a b x, begin
    simp_rw [mem_map, exists_prop, mem_range, int.lt_to_nat, function.embedding.trans_apply,
      nat.cast_embedding_apply, add_left_embedding_apply, nat_cast_eq_coe_nat],
    split,
    { rintro ⟨a, h, rfl⟩,
      rw [←add_one_le_iff, le_sub_iff_add_le', add_comm _ (1 : ℤ), ←add_assoc] at h,
      exact ⟨int.le.intro rfl, h⟩ },
    { rintro ⟨ha, hb⟩,
      use (x - (a + 1)).to_nat,
      rw [to_nat_sub_of_le ha, ←add_one_le_iff, sub_add, add_sub_cancel],
      exact ⟨sub_le_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end,
  finset_mem_Ioo := λ a b x, begin
    simp_rw [mem_map, exists_prop, mem_range, int.lt_to_nat, function.embedding.trans_apply,
      nat.cast_embedding_apply, add_left_embedding_apply, nat_cast_eq_coe_nat],
    split,
    { rintro ⟨a, h, rfl⟩,
      rw [sub_sub, lt_sub_iff_add_lt'] at h,
      exact ⟨int.le.intro rfl, h⟩ },
    { rintro ⟨ha, hb⟩,
      use (x - (a + 1)).to_nat,
      rw [to_nat_sub_of_le ha, sub_sub],
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end }

namespace int
variables (a b : ℤ)

lemma Icc_eq_finset_map :
  Icc a b = (finset.range (b + 1 - a).to_nat).map
    (nat.cast_embedding.trans $ add_left_embedding a) := rfl
lemma Ico_eq_finset_map :
  Ico a b = (finset.range (b - a).to_nat).map
    (nat.cast_embedding.trans $ add_left_embedding a) := rfl
lemma Ioc_eq_finset_map :
  Ioc a b = (finset.range (b - a).to_nat).map
    (nat.cast_embedding.trans $ add_left_embedding (a + 1)) := rfl
lemma Ioo_eq_finset_map :
  Ioo a b = (finset.range (b - a - 1).to_nat).map
    (nat.cast_embedding.trans $ add_left_embedding (a + 1)) := rfl

@[simp] lemma card_Icc : (Icc a b).card = (b + 1 - a).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_Ico : (Ico a b).card = (b - a).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_Ioc : (Ioc a b).card = (b - a).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_Ioo : (Ioo a b).card = (b - a - 1).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

lemma card_Icc_of_le (h : a ≤ b + 1) : ((Icc a b).card : ℤ) = b + 1 - a :=
by rw [card_Icc, to_nat_sub_of_le h]

lemma card_Ico_of_le (h : a ≤ b) : ((Ico a b).card : ℤ) = b - a :=
by rw [card_Ico, to_nat_sub_of_le h]

lemma card_Ioc_of_le (h : a ≤ b) : ((Ioc a b).card : ℤ) = b - a :=
by rw [card_Ioc, to_nat_sub_of_le h]

lemma card_Ioo_of_lt (h : a < b) : ((Ioo a b).card : ℤ) = b - a - 1 :=
by rw [card_Ioo, sub_sub, to_nat_sub_of_le h]

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = (b + 1 - a).to_nat :=
by rw [←card_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = (b - a).to_nat :=
by rw [←card_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = (b - a).to_nat :=
by rw [←card_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = (b - a - 1).to_nat :=
by rw [←card_Ioo, fintype.card_of_finset]

lemma card_fintype_Icc_of_le (h : a ≤ b + 1) : (fintype.card (set.Icc a b) : ℤ) = b + 1 - a :=
by rw [card_fintype_Icc, to_nat_sub_of_le h]

lemma card_fintype_Ico_of_le (h : a ≤ b) : (fintype.card (set.Ico a b) : ℤ) = b - a :=
by rw [card_fintype_Ico, to_nat_sub_of_le h]

lemma card_fintype_Ioc_of_le (h : a ≤ b) : (fintype.card (set.Ioc a b) : ℤ) = b - a :=
by rw [card_fintype_Ioc, to_nat_sub_of_le h]

lemma card_fintype_Ioo_of_lt (h : a < b) : (fintype.card (set.Ioo a b) : ℤ) = b - a - 1 :=
by rw [card_fintype_Ioo, sub_sub, to_nat_sub_of_le h]

end int

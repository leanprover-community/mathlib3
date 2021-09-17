/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.int.basic
import data.nat.intervals

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open finset int
private lemma inj (a : ℤ) : function.injective (λ n : ℕ, (n : ℤ) + a) :=
λ m n, by { rw [add_left_inj, coe_nat_inj'], exact id }

instance : locally_finite_order ℤ :=
{ finset_Icc := λ a b, (finset.range (b + 1 - a).to_nat).map
    ⟨λ n, n + a, inj a⟩,
  finset_Ico := λ a b, (finset.range (b - a).to_nat).map
    ⟨λ n, n + a, inj a⟩,
  finset_Ioc := λ a b, (finset.range (b - a).to_nat).map
    ⟨λ n, n + (a + 1), inj (a + 1)⟩,
  finset_Ioo := λ a b, (finset.range (b - a - 1).to_nat).map
    ⟨λ n, n + (a + 1), inj (a + 1)⟩,
  finset_mem_Icc := λ a b x, begin
    simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
      mem_map],
    split,
    { rintro ⟨a, h, rfl⟩,
      rw [lt_sub_iff_add_lt, int.lt_add_one_iff, add_comm] at h,
      refine ⟨int.le.intro rfl, h⟩ },
    { rintro ⟨ha, hb⟩,
      use (x - a).to_nat,
      rw to_nat_sub_of_le ha,
      rw ←lt_add_one_iff at hb,
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end,
  finset_mem_Ico := λ a b x, begin
    simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
      mem_map],
    split,
    { rintro ⟨a, h, rfl⟩,
      exact ⟨int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩ },
    { rintro ⟨ha, hb⟩,
      use (x - a).to_nat,
      rw to_nat_sub_of_le ha,
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end,
  finset_mem_Ioc := λ a b x, begin
    simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
      mem_map],
    split,
    { rintro ⟨a, h, rfl⟩,
      refine ⟨int.le.intro rfl, _⟩,
      rwa [←add_one_le_iff, le_sub_iff_add_le', add_comm _ (1 : ℤ), ←add_assoc] at h },
    { rintro ⟨ha, hb⟩,
      use (x - (a + 1)).to_nat,
      rw [to_nat_sub_of_le ha, ←add_one_le_iff, sub_add, add_sub_cancel],
      exact ⟨sub_le_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end,
  finset_mem_Ioo := λ a b x, begin
    simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
      mem_map],
    split,
    { rintro ⟨a, h, rfl⟩,
      refine ⟨int.le.intro rfl, _⟩,
      rwa [sub_sub, lt_sub_iff_add_lt'] at h },
    { rintro ⟨ha, hb⟩,
      use (x - (a + 1)).to_nat,
      rw [to_nat_sub_of_le ha, sub_sub],
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩ }
  end }

namespace int
variables (a b : ℤ)

lemma Icc_eq_finset_map : Icc a b = (finset.range (b + 1 - a).to_nat).map ⟨λ n, n + a, inj a⟩ := rfl
lemma Ico_eq_finset_map : Ico a b = (finset.range (b - a).to_nat).map ⟨λ n, n + a, inj a⟩ := rfl
lemma Ioc_eq_finset_map : Ioc a b = (finset.range (b - a).to_nat).map ⟨λ n, n + (a + 1), inj _⟩ :=
rfl
lemma Ioo_eq_finset_map : Ioo a b = (finset.range (b - a - 1).to_nat).map
  ⟨λ n, n + (a + 1), inj _⟩ :=
rfl

@[simp] lemma card_Icc : (Icc a b).card = (b + 1 - a).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_Ico : (Ico a b).card = (b - a).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_Ioc : (Ioc a b).card = (b - a).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_Ioo : (Ioo a b).card = (b - a - 1).to_nat :=
by { change (finset.map _ _).card = _, rw [finset.card_map, finset.card_range] }

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = (b + 1 - a).to_nat :=
by rw [←card_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = (b - a).to_nat :=
by rw [←card_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = (b - a).to_nat :=
by rw [←card_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = (b - a - 1).to_nat :=
by rw [←card_Ioo, fintype.card_of_finset]

end int

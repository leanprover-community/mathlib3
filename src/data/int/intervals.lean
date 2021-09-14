/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.int.basic
import order.locally_finite

/-!
# Intervals of integers

This file proves that `ℤ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open finset int

instance : locally_finite_order ℤ :=
{ finset_Icc := λ a b, (Iio (b + 1 - a).to_nat).map ⟨λ n, n + a, λ _, by simp only
  [imp_self, forall_const, add_left_inj, int.coe_nat_inj']⟩,
  finset_mem_Icc := λ a b x, begin
    rw [mem_map, set.mem_Icc, function.embedding.coe_fn_mk],
    split,
    { rintro ⟨n, hn, hx⟩,
      rw [←hx, le_add_iff_nonneg_left],
      rw [mem_Iio_iff, int.lt_to_nat, lt_sub_iff_add_lt, int.lt_add_one_iff] at hn,
      exact ⟨int.coe_nat_nonneg _, hn⟩ },
    rintro h,
    refine ⟨(x - a).to_nat, _, by rw [int.to_nat_sub_of_le h.1, int.sub_add_cancel]⟩,
    rw mem_Iio_iff,
    have hb := int.lt_add_one_of_le h.2,
    exact (int.to_nat_lt_to_nat (sub_pos.2 (h.1.trans_lt hb))).2 (sub_lt_sub_right hb _),
  end }

namespace int
variables (a b : ℤ)

/-- `int_Ico a b` is the set of integers `b ≤ k < a`. -/
def int_Ico (a b : ℤ) : finset ℤ :=
(finset.range (b - a).to_nat).map
  { to_fun := λ n, n + b,
    inj' := λ n m h, by simpa using h }

@[simp] lemma int_Ico.mem {n m l : ℤ} : l ∈ int_Ico n m ↔ n ≤ l ∧ l < m :=
begin
  dsimp [int_Ico],
  simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
    mem_map],
  split,
  { rintro ⟨a, ⟨h, rfl⟩⟩,
    exact ⟨int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩ },
  { rintro ⟨h₁, h₂⟩,
    use (l - n).to_nat,
    split; simp [h₁, h₂], }
end

@[simp] lemma int_Ico.card (a b : ℤ) : (int_Ico a b).card = (b - a).to_nat := by simp [int_Ico]

@[simp] lemma card_finset_Icc : (Icc a b).card = (b + 1 - a).to_nat := sorry

@[simp] lemma card_finset_Ico : (Ico a b).card = (b - a).to_nat := sorry

@[simp] lemma card_finset_Ioc : (Ioc a b).card = (b - a).to_nat := sorry

@[simp] lemma card_finset_Ioo : (Ioo a b).card = (b - a - 1).to_nat := sorry

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = (b + 1 - a).to_nat :=
by rw [←card_finset_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = (b - a).to_nat :=
by rw [←card_finset_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = (b - a).to_nat :=
by rw [←card_finset_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = (b - a - 1).to_nat :=
by rw [←card_finset_Ioo, fintype.card_of_finset]

end int

/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies
-/
import data.nat.intervals

/-!
# Intervals of positive naturals

This file proves that `ℕ+` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open finset pnat

instance : locally_finite_order ℕ+ := subtype.locally_finite_order _

namespace pnat
variables (a b : ℕ+)

@[simp] lemma card_finset_Icc : (Icc a b).card = b + 1 - a :=
begin
  change (finset.subtype _ _).card = _,
  rw [finset.card_subtype, finset.filter_true_of_mem, nat.card_finset_Icc], refl,
  exact λ x hx, a.2.trans_le (mem_Icc.1 hx).1,
end

@[simp] lemma card_finset_Ico : (Ico a b).card = b - a :=
begin
  change (finset.subtype _ _).card = _,
  rw [finset.card_subtype, finset.filter_true_of_mem, nat.card_finset_Ico], refl,
  exact λ x hx, a.2.trans_le (mem_Ico.1 hx).1,
end

@[simp] lemma card_finset_Ioc : (Ioc a b).card = b - a :=
begin
  change (finset.subtype _ _).card = _,
  rw [finset.card_subtype, finset.filter_true_of_mem, nat.card_finset_Ioc], refl,
  exact λ x hx, a.2.trans (mem_Ioc.1 hx).1,
end

@[simp] lemma card_finset_Ioo : (Ioo a b).card = b - a - 1 :=
begin
  change (finset.subtype _ _).card = _,
  rw [finset.card_subtype, finset.filter_true_of_mem, nat.card_finset_Ioo], refl,
  exact λ x hx, a.2.trans (mem_Ioo.1 hx).1,
end

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [←card_finset_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = b - a :=
by rw [←card_finset_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [←card_finset_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [←card_finset_Ioo, fintype.card_of_finset]

end pnat

/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite
import data.fintype.card

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/

open finset fintype
open_locale big_operators

variables {ι : Type*} {α : ι → Type*} [decidable_eq ι] [fintype ι] [Π i, decidable_eq (α i)]
  [Π i, partial_order (α i)] [Π i, locally_finite_order (α i)]

namespace pi

instance : locally_finite_order (Π i, α i) :=
locally_finite_order.of_Icc _
  (λ a b, pi_finset $ λ i, Icc (a i) (b i))
  (λ a b x, by { simp_rw [mem_pi_finset, mem_Icc], exact forall_and_distrib })

variables (a b : Π i, α i)

lemma card_Icc : (Icc a b).card = ∏ i, (Icc (a i) (b i)).card := card_pi_finset _

lemma card_Ico : (Ico a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc : (Ioc a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo : (Ioo a b).card = (∏ i, (Icc (a i) (b i)).card) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end pi

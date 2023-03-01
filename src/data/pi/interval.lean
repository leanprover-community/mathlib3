/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite
import data.fintype.big_operators

/-!
# Intervals in a pi type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/

open finset fintype
open_locale big_operators

variables {ι : Type*} {α : ι → Type*}


namespace pi

section locally_finite
variables [decidable_eq ι] [fintype ι] [Π i, decidable_eq (α i)]
  [Π i, partial_order (α i)] [Π i, locally_finite_order (α i)]

instance : locally_finite_order (Π i, α i) :=
locally_finite_order.of_Icc _
  (λ a b, pi_finset $ λ i, Icc (a i) (b i))
  (λ a b x, by simp_rw [mem_pi_finset, mem_Icc, le_def, forall_and_distrib])

variables (a b : Π i, α i)

lemma Icc_eq : Icc a b = pi_finset (λ i, Icc (a i) (b i)) := rfl

lemma card_Icc : (Icc a b).card = ∏ i, (Icc (a i) (b i)).card := card_pi_finset _

lemma card_Ico : (Ico a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc : (Ioc a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo : (Ioo a b).card = (∏ i, (Icc (a i) (b i)).card) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end locally_finite

section bounded
variables [decidable_eq ι] [fintype ι] [Π i, decidable_eq (α i)] [Π i, partial_order (α i)]

section bot
variables [Π i, locally_finite_order_bot (α i)] (b : Π i, α i)

instance : locally_finite_order_bot (Π i, α i) :=
locally_finite_order_top.of_Iic _
  (λ b, pi_finset $ λ i, Iic (b i))
  (λ b x, by simp_rw [mem_pi_finset, mem_Iic, le_def])

lemma card_Iic : (Iic b).card = ∏ i, (Iic (b i)).card := card_pi_finset _

lemma card_Iio : (Iio b).card = (∏ i, (Iic (b i)).card) - 1 :=
by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end bot

section top
variables [Π i, locally_finite_order_top (α i)] (a : Π i, α i)

instance : locally_finite_order_top (Π i, α i) :=
locally_finite_order_top.of_Ici _
  (λ a, pi_finset $ λ i, Ici (a i))
  (λ a x, by simp_rw [mem_pi_finset, mem_Ici, le_def])

lemma card_Ici : (Ici a).card = (∏ i, (Ici (a i)).card) := card_pi_finset _

lemma card_Ioi : (Ioi a).card = (∏ i, (Ici (a i)).card) - 1 :=
by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

end top

end bounded

end pi

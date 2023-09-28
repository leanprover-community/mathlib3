/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.big_operators.ring

/-!
# Stuff for algebra.big_operators.ring
-/

open_locale big_operators

lemma sum_tsub {α β : Type*} [add_comm_monoid β] [partial_order β] [has_exists_add_of_le β]
  [covariant_class β β (+) (≤)] [contravariant_class β β (+) (≤)] [has_sub β] [has_ordered_sub β]
  (s : finset α) {f g : α → β} (hfg : ∀ x ∈ s, g x ≤ f x) :
  ∑ x in s, (f x - g x) = ∑ x in s, f x - ∑ x in s, g x :=
eq_tsub_of_add_eq $ by rw [←finset.sum_add_distrib];
  exact finset.sum_congr rfl (λ x hx, tsub_add_cancel_of_le $ hfg _ hx)

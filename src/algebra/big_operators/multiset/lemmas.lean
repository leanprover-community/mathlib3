/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
import data.list.big_operators.lemmas
import algebra.big_operators.multiset.basic

/-! # Lemmas about `multiset.sum` and `multiset.prod` requiring extra algebra imports 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

variables {ι α β γ : Type*}

namespace multiset

lemma dvd_prod [comm_monoid α] {s : multiset α} {a : α}  : a ∈ s → a ∣ s.prod :=
quotient.induction_on s (λ l a h, by simpa using list.dvd_prod h) a

@[to_additive]
lemma prod_eq_one_iff [canonically_ordered_monoid α] {m : multiset α} :
  m.prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
quotient.induction_on m $ λ l, by simpa using list.prod_eq_one_iff l

end multiset

open multiset

namespace commute
variables [non_unital_non_assoc_semiring α] {a : α} {s : multiset ι} {f : ι → α}

lemma multiset_sum_right (s : multiset α) (a : α) (h : ∀ b ∈ s, commute a b) :
  commute a s.sum :=
begin
  induction s using quotient.induction_on,
  rw [quot_mk_to_coe, coe_sum],
  exact commute.list_sum_right _ _ h,
end

lemma multiset_sum_left (s : multiset α) (b : α) (h : ∀ a ∈ s, commute a b) :
  commute s.sum b :=
(commute.multiset_sum_right _ _ $ λ a ha, (h _ ha).symm).symm

end commute

/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.order

/-!
# Double countings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : finset α` and `t : finset β` by the minimum/maximum of edges over all `a ∈ s` times the
the size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartite_below`: `s.bipartite_below r b` are the elements of `s` below `b` wrt to `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartite_above`: `t.bipartite_above r a` are the elements of `t` above `a` wrt to `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.
-/

open finset function relator
open_locale big_operators

variables {α β : Type*}

/-! ### Bipartite graph -/

namespace finset
section bipartite
variables (r : α → β → Prop) (s : finset α) (t : finset β) (a a' : α) (b b' : β)
  [decidable_pred (r a)] [Π a, decidable (r a b)] {m n : ℕ}

/-- Elements of `s` which are "below" `b` according to relation `r`. -/
def bipartite_below : finset α := s.filter (λ a, r a b)

/-- Elements of `t` which are "above" `a` according to relation `r`. -/
def bipartite_above : finset β := t.filter (r a)

lemma bipartite_below_swap : t.bipartite_below (swap r) a = t.bipartite_above r a := rfl
lemma bipartite_above_swap : s.bipartite_above (swap r) b = s.bipartite_below r b := rfl

@[simp, norm_cast] lemma coe_bipartite_below : (s.bipartite_below r b : set α) = {a ∈ s | r a b} :=
coe_filter _ _

@[simp, norm_cast] lemma coe_bipartite_above : (t.bipartite_above r a : set β) = {b ∈ t | r a b} :=
coe_filter _ _

variables {s t a a' b b'}

@[simp] lemma mem_bipartite_below {a : α} : a ∈ s.bipartite_below r b ↔ a ∈ s ∧ r a b := mem_filter
@[simp] lemma mem_bipartite_above {b : β} : b ∈ t.bipartite_above r a ↔ b ∈ t ∧ r a b := mem_filter

lemma sum_card_bipartite_above_eq_sum_card_bipartite_below [Π a b, decidable (r a b)] :
  ∑ a in s, (t.bipartite_above r a).card = ∑ b in t, (s.bipartite_below r b).card :=
by { simp_rw [card_eq_sum_ones, bipartite_above, bipartite_below, sum_filter], exact sum_comm }

/-- Double counting argument. Considering `r` as a bipartite graph, the LHS is a lower bound on the
number of edges while the RHS is an upper bound. -/
lemma card_mul_le_card_mul [Π a b, decidable (r a b)]
  (hm : ∀ a ∈ s, m ≤ (t.bipartite_above r a).card)
  (hn : ∀ b ∈ t, (s.bipartite_below r b).card ≤ n) :
  s.card * m ≤ t.card * n :=
calc
    _ ≤ ∑ a in s, (t.bipartite_above r a).card : s.card_nsmul_le_sum _ _ hm
  ... = ∑ b in t, (s.bipartite_below r b).card
      : sum_card_bipartite_above_eq_sum_card_bipartite_below _
  ... ≤ _ : t.sum_le_card_nsmul _ _ hn

lemma card_mul_le_card_mul' [Π a b, decidable (r a b)]
  (hn : ∀ b ∈ t, n ≤ (s.bipartite_below r b).card)
  (hm : ∀ a ∈ s, (t.bipartite_above r a).card ≤ m) :
  t.card * n ≤ s.card * m :=
card_mul_le_card_mul (swap r) hn hm

lemma card_mul_eq_card_mul [Π a b, decidable (r a b)]
  (hm : ∀ a ∈ s, (t.bipartite_above r a).card = m)
  (hn : ∀ b ∈ t, (s.bipartite_below r b).card = n) :
  s.card * m = t.card * n :=
(card_mul_le_card_mul _ (λ a ha, (hm a ha).ge) $ λ b hb, (hn b hb).le).antisymm $
  card_mul_le_card_mul' _ (λ a ha, (hn a ha).ge) $ λ b hb, (hm b hb).le

lemma card_le_card_of_forall_subsingleton
  (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b) (ht : ∀ b ∈ t, ({a ∈ s | r a b} : set α).subsingleton) :
  s.card ≤ t.card :=
by classical; simpa using card_mul_le_card_mul _ (λ a h, card_pos.2 $
  (by { rw [←coe_nonempty, coe_bipartite_above], exact hs _ h } : (t.bipartite_above r a).nonempty))
  (λ b h, card_le_one.2 $ by { simp_rw mem_bipartite_below, exact ht _ h })

lemma card_le_card_of_forall_subsingleton'
  (ht : ∀ b ∈ t, ∃ a, a ∈ s ∧ r a b) (hs : ∀ a ∈ s, ({b ∈ t | r a b} : set β).subsingleton) :
  t.card ≤ s.card :=
card_le_card_of_forall_subsingleton (swap r) ht hs

end bipartite
end finset

open finset

namespace fintype
variables [fintype α] [fintype β] {r : α → β → Prop}

lemma card_le_card_of_left_total_unique (h₁ : left_total r) (h₂ : left_unique r) :
  fintype.card α ≤ fintype.card β :=
card_le_card_of_forall_subsingleton r (by simpa using h₁) $ λ b _ a₁ ha₁ a₂ ha₂, h₂ ha₁.2 ha₂.2

lemma card_le_card_of_right_total_unique (h₁ : right_total r) (h₂ : right_unique r) :
  fintype.card β ≤ fintype.card α :=
card_le_card_of_forall_subsingleton' r (by simpa using h₁) $ λ b _ a₁ ha₁ a₂ ha₂, h₂ ha₁.2 ha₂.2

end fintype


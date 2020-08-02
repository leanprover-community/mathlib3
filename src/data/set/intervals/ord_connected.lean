/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import data.set.intervals.unordered_interval
import data.set.lattice

/-!
# Order-connected sets

We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α = ℝ`, then
this condition is also equivalent to `convex s`.

In this file we prove that intersection of a family of `ord_connected` sets is `ord_connected` and
that all standard intervals are `ord_connected`.
-/

namespace set

variables {α : Type*} [preorder α] {s t : set α}

/--
We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α = ℝ`, then
this condition is also equivalent to `convex s`.
-/
def ord_connected (s : set α) : Prop := ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s

/-- It suffices to prove `[x, y] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
lemma ord_connected_iff : ord_connected s ↔ ∀ (x ∈ s) (y ∈ s), x ≤ y → Icc x y ⊆ s :=
⟨λ hs x hx y hy hxy, hs hx hy, λ H x hx y hy z hz, H x hx y hy (le_trans hz.1 hz.2) hz⟩

lemma ord_connected_of_Ioo {α : Type*} [partial_order α] {s : set α}
  (hs : ∀ (x ∈ s) (y ∈ s), x < y → Ioo x y ⊆ s) :
  ord_connected s :=
begin
  rw ord_connected_iff,
  intros x hx y hy hxy,
  rcases eq_or_lt_of_le hxy with rfl|hxy', { simpa },
  have := hs x hx y hy hxy',
  rw [← union_diff_cancel Ioo_subset_Icc_self],
  simp [*, insert_subset]
end

lemma ord_connected.inter {s t : set α} (hs : ord_connected s) (ht : ord_connected t) :
  ord_connected (s ∩ t) :=
λ x hx y hy, subset_inter (hs hx.1 hy.1) (ht hx.2 hy.2)

lemma ord_connected.dual {s : set α} (hs : ord_connected s) : @ord_connected (order_dual α) _ s :=
λ x hx y hy z hz, hs hy hx ⟨hz.2, hz.1⟩

lemma ord_connected_dual {s : set α} : @ord_connected (order_dual α) _ s ↔ ord_connected s :=
⟨λ h, h.dual, λ h, h.dual⟩

lemma ord_connected_sInter {S : set (set α)} (hS : ∀ s ∈ S, ord_connected s) :
  ord_connected (⋂₀ S) :=
λ x hx y hy, subset_sInter $ λ s hs, hS s hs (hx s hs) (hy s hs)

lemma ord_connected_Inter {ι : Sort*} {s : ι → set α} (hs : ∀ i, ord_connected (s i)) :
  ord_connected (⋂ i, s i) :=
ord_connected_sInter $ forall_range_iff.2 hs

lemma ord_connected_bInter {ι : Sort*} {p : ι → Prop} {s : Π (i : ι) (hi : p i), set α}
  (hs : ∀ i hi, ord_connected (s i hi)) :
  ord_connected (⋂ i hi, s i hi) :=
ord_connected_Inter $ λ i, ord_connected_Inter $ hs i

lemma ord_connected_Ici {a : α} : ord_connected (Ici a) := λ x hx y hy z hz, le_trans hx hz.1
lemma ord_connected_Iic {a : α} : ord_connected (Iic a) := λ x hx y hy z hz, le_trans hz.2 hy
lemma ord_connected_Ioi {a : α} : ord_connected (Ioi a) := λ x hx y hy z hz, lt_of_lt_of_le hx hz.1
lemma ord_connected_Iio {a : α} : ord_connected (Iio a) := λ x hx y hy z hz, lt_of_le_of_lt hz.2 hy

lemma ord_connected_Icc {a b : α} : ord_connected (Icc a b) :=
ord_connected_Ici.inter ord_connected_Iic

lemma ord_connected_Ico {a b : α} : ord_connected (Ico a b) :=
ord_connected_Ici.inter ord_connected_Iio

lemma ord_connected_Ioc {a b : α} : ord_connected (Ioc a b) :=
ord_connected_Ioi.inter ord_connected_Iic

lemma ord_connected_Ioo {a b : α} : ord_connected (Ioo a b) :=
ord_connected_Ioi.inter ord_connected_Iio

lemma ord_connected_empty : ord_connected (∅ : set α) := λ x, false.elim

lemma ord_connected_univ : ord_connected (univ : set α) := λ _ _ _ _, subset_univ _

variables {β : Type*} [decidable_linear_order β]

lemma ord_connected_interval {a b : β} : ord_connected (interval a b) :=
ord_connected_Icc

lemma ord_connected.interval_subset {s : set β} (hs : ord_connected s)
  ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
  interval x y ⊆ s :=
by cases le_total x y; simp only [interval_of_le, interval_of_ge, *]; apply hs; assumption

lemma ord_connected_iff_interval_subset {s : set β} :
  ord_connected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), interval x y ⊆ s :=
⟨λ h, h.interval_subset,
  λ h, ord_connected_iff.2 $ λ x hx y hy hxy, by simpa only [interval_of_le hxy] using h hx hy⟩

end set

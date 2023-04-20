/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.antichain
import order.upper_lower.basic

/-!
# Minimal/maximal elements of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines minimal and maximal of a set with respect to an arbitrary relation.

## Main declarations

* `maximals r s`: Maximal elements of `s` with respect to `r`.
* `minimals r s`: Minimal elements of `s` with respect to `r`.

## TODO

Do we need a `finset` version?
-/

open function set

variables {α : Type*} (r r₁ r₂ : α → α → Prop) (s t : set α) (a b : α)

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
def maximals : set α := {a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → r b a}

/-- Turns a set into an antichain by keeping only the "minimal" elements. -/
def minimals : set α := {a ∈ s | ∀ ⦃b⦄, b ∈ s → r b a → r a b}

lemma maximals_subset : maximals r s ⊆ s := sep_subset _ _
lemma minimals_subset : minimals r s ⊆ s := sep_subset _ _

@[simp] lemma maximals_empty : maximals r ∅ = ∅ := sep_empty _
@[simp] lemma minimals_empty : minimals r ∅ = ∅ := sep_empty _

@[simp] lemma maximals_singleton : maximals r {a} = {a} :=
(maximals_subset _ _).antisymm $ singleton_subset_iff.2 $
  ⟨rfl, by { rintro b (rfl : b = a), exact id }⟩

@[simp] lemma minimals_singleton : minimals r {a} = {a} := maximals_singleton _ _

lemma maximals_swap : maximals (swap r) s = minimals r s := rfl
lemma minimals_swap : minimals (swap r) s = maximals r s := rfl

section is_antisymm
variables {r s t a b} [is_antisymm α r]

lemma eq_of_mem_maximals (ha : a ∈ maximals r s) (hb : b ∈ s) (h : r a b) : a = b :=
antisymm h $ ha.2 hb h

lemma eq_of_mem_minimals (ha : a ∈ minimals r s) (hb : b ∈ s) (h : r b a) : a = b :=
antisymm (ha.2 hb h) h

variables (r s)

lemma maximals_antichain : is_antichain r (maximals r s) :=
λ a ha b hb hab h, hab $ eq_of_mem_maximals ha hb.1 h

lemma minimals_antichain : is_antichain r (minimals r s) :=
by { haveI := is_antisymm.swap r, exact (maximals_antichain _ _).swap }

end is_antisymm

lemma maximals_eq_minimals [is_symm α r] : maximals r s = minimals r s :=
by { congr, ext a b, exact comm }

variables {r r₁ r₂ s t a}

lemma set.subsingleton.maximals_eq (h : s.subsingleton) : maximals r s = s :=
h.induction_on (minimals_empty _) (maximals_singleton _)

lemma set.subsingleton.minimals_eq (h : s.subsingleton) : minimals r s = s := h.maximals_eq

lemma maximals_mono [is_antisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
  maximals r₂ s ⊆ maximals r₁ s :=
λ a ha, ⟨ha.1, λ b hb hab,
  by { have := eq_of_mem_maximals ha hb (h _ _ hab), subst this, exact hab }⟩

lemma minimals_mono [is_antisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
  minimals r₂ s ⊆ minimals r₁ s :=
λ a ha, ⟨ha.1, λ b hb hab,
  by { have := eq_of_mem_minimals ha hb (h _ _ hab), subst this, exact hab }⟩

lemma maximals_union : maximals r (s ∪ t) ⊆ maximals r s ∪ maximals r t :=
begin
  intros a ha,
  obtain h | h := ha.1,
  { exact or.inl ⟨h, λ b hb, ha.2 $ or.inl hb⟩ },
  { exact or.inr ⟨h, λ b hb, ha.2 $ or.inr hb⟩ }
end

lemma minimals_union : minimals r (s ∪ t) ⊆ minimals r s ∪ minimals r t := maximals_union

lemma maximals_inter_subset : maximals r s ∩ t ⊆ maximals r (s ∩ t) :=
λ a ha, ⟨⟨ha.1.1, ha.2⟩, λ b hb, ha.1.2 hb.1⟩

lemma minimals_inter_subset : minimals r s ∩ t ⊆ minimals r (s ∩ t) := maximals_inter_subset

lemma inter_maximals_subset : s ∩ maximals r t ⊆ maximals r (s ∩ t) :=
λ a ha, ⟨⟨ha.1, ha.2.1⟩, λ b hb, ha.2.2 hb.2⟩

lemma inter_minimals_subset : s ∩ minimals r t ⊆ minimals r (s ∩ t) := inter_maximals_subset

lemma _root_.is_antichain.maximals_eq (h : is_antichain r s) : maximals r s = s :=
(maximals_subset _ _).antisymm $ λ a ha, ⟨ha, λ b hb hab,
  by { have := h.eq ha hb hab, subst this, exact hab }⟩

lemma _root_.is_antichain.minimals_eq (h : is_antichain r s) : minimals r s = s :=
(minimals_subset _ _).antisymm $ λ a ha, ⟨ha, λ b hb hab,
  by { have := h.eq hb ha hab, subst this, exact hab }⟩

@[simp] lemma maximals_idem : maximals r (maximals r s) = maximals r s :=
(maximals_subset _ _).antisymm $ λ a ha, ⟨ha, λ b hb, ha.2 hb.1⟩

@[simp] lemma minimals_idem : minimals r (minimals r s) = minimals r s := maximals_idem

/-- If `maximals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
lemma is_antichain.max_maximals (ht : is_antichain r t) (h : maximals r s ⊆ t)
  (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ maximals r s, r b a) :
  maximals r s = t :=
begin
  refine h.antisymm (λ a ha, _),
  obtain ⟨b, hb, hr⟩ := hs ha,
  rwa of_not_not (λ hab, ht (h hb) ha (ne.symm hab) hr),
end

/-- If `minimals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
lemma is_antichain.max_minimals (ht : is_antichain r t) (h : minimals r s ⊆ t)
  (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ minimals r s, r a b) :
  minimals r s = t :=
begin
  refine h.antisymm (λ a ha, _),
  obtain ⟨b, hb, hr⟩ := hs ha,
  rwa of_not_not (λ hab, ht ha (h hb) hab hr),
end

variables [partial_order α]

lemma is_least.mem_minimals (h : is_least s a) : a ∈ minimals (≤) s := ⟨h.1, λ b hb _, h.2 hb⟩
lemma is_greatest.mem_maximals (h : is_greatest s a) : a ∈ maximals (≤) s := ⟨h.1, λ b hb _, h.2 hb⟩

lemma is_least.minimals_eq (h : is_least s a) : minimals (≤) s = {a} :=
eq_singleton_iff_unique_mem.2 ⟨h.mem_minimals, λ b hb, eq_of_mem_minimals hb h.1 $ h.2 hb.1⟩

lemma is_greatest.maximals_eq (h : is_greatest s a) : maximals (≤) s = {a} :=
eq_singleton_iff_unique_mem.2 ⟨h.mem_maximals, λ b hb, eq_of_mem_maximals hb h.1 $ h.2 hb.1⟩

lemma is_antichain.minimals_upper_closure (hs : is_antichain (≤) s) :
  minimals (≤) (upper_closure s : set α) = s :=
hs.max_minimals (λ a ⟨⟨b, hb, hba⟩, h⟩, by rwa eq_of_mem_minimals ‹a ∈ _› (subset_upper_closure hb)
  hba) $ λ a ha, ⟨a, ⟨subset_upper_closure ha, λ b ⟨c, hc, hcb⟩ hba,
    by rwa hs.eq' ha hc (hcb.trans hba)⟩, le_rfl⟩

lemma is_antichain.maximals_lower_closure (hs : is_antichain (≤) s) :
  maximals (≤) (lower_closure s : set α) = s :=
hs.to_dual.minimals_upper_closure
